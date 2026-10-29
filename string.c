// SPDX-License-Identifier: GPL-3.0-or-later
/*
 * string: 从已解码的语言 FF 流导出 type58 本地化字符串，
 * 写成按 key 排序的 TSV（key、name、text 三列）。
 *
 * 条目头 16 字节：+0 为 key，+8 低位为文本 ID，
 * bit61 表示文本内联。非内联条目引用同包中
 * 更早出现的同 ID 文本。key 是名称的 native 路径
 * hash（libgame sub_1718510），-n 给出的候选
 * 只有 hash 精确命中才采用。
 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <ftw.h>
#include <getopt.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#define PTR_FULL	0x7fffffffffffffffULL
#define PTR_DEFAULT	0x3fffffffffffffffULL
#define PTR_INLINE	(1ULL << 61)
#define ARRAY_MAX	1000000U
#define STRING_MAX	(1024 * 1024)
#define NAME_TOKEN_MAX	201

#define TYPE_IMAGE	17
#define TYPE_LOCALIZE	58
#define TYPE_RAWFILE	67
#define TYPE_NETCONST	74
#define TYPE_KVP	121

/* 不支持的类型只停止该包，其余错误整体失败。 */
enum {
	PARSE_OK,
	PARSE_UNSUPPORTED,
	PARSE_ERROR,
};

struct reader {
	const uint8_t *data;
	size_t len;
	size_t pos;
	const char *path;
};

struct row {
	uint64_t key;
	const uint8_t *text;
	size_t len;
};

struct token {
	const uint8_t *str;
	size_t len;
};

struct slot {
	uint64_t key;
	const uint8_t *str;
	size_t len;
	bool used;
};

struct map {
	struct slot *slots;
	size_t mask;
};

struct package {
	size_t declared;
	size_t extracted;
	size_t inlined;
	size_t referenced;
	size_t unresolved;
	bool stopped;
	size_t stop_index;
	uint32_t stop_type;
	struct map ids;
};

static struct row *rows;
static size_t nr_rows, cap_rows;
static struct token *tokens;
static size_t nr_tokens, cap_tokens;
static struct map key_names;
static size_t name_files;

static void __attribute__((noreturn)) die(const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	fputs("string: ", stderr);
	vfprintf(stderr, fmt, ap);
	fputc('\n', stderr);
	va_end(ap);
	exit(2);
}

static void *xrealloc(void *ptr, size_t nmemb, size_t size)
{
	ptr = reallocarray(ptr, nmemb, size);
	if (!ptr)
		die("内存不足");
	return ptr;
}

static void push_row(uint64_t key, const uint8_t *text, size_t len)
{
	if (nr_rows == cap_rows) {
		cap_rows = cap_rows ? cap_rows * 2 : 4096;
		rows = xrealloc(rows, cap_rows, sizeof(*rows));
	}
	rows[nr_rows++] = (struct row){ key, text, len };
}

static void push_token(const uint8_t *str, size_t len)
{
	if (nr_tokens == cap_tokens) {
		cap_tokens = cap_tokens ? cap_tokens * 2 : 1024;
		tokens = xrealloc(tokens, cap_tokens, sizeof(*tokens));
	}
	tokens[nr_tokens++] = (struct token){ str, len };
}

/* 开放寻址；容量大于条目数两倍，总有空槽。 */
static void map_init(struct map *map, size_t entries)
{
	size_t cap = 16;

	while (cap < entries * 2 + 1)
		cap *= 2;
	map->slots = calloc(cap, sizeof(*map->slots));
	if (!map->slots)
		die("内存不足");
	map->mask = cap - 1;
}

static void map_free(struct map *map)
{
	free(map->slots);
	map->slots = NULL;
}

static struct slot *map_slot(struct map *map, uint64_t key)
{
	uint64_t h = key * 0x9e3779b97f4a7c15ULL;
	size_t i = (h ^ (h >> 32)) & map->mask;

	while (map->slots[i].used && map->slots[i].key != key)
		i = (i + 1) & map->mask;
	return &map->slots[i];
}

static uint64_t get_le(const uint8_t *p, int bytes)
{
	uint64_t v = 0;

	while (bytes--)
		v = (v << 8) | p[bytes];
	return v;
}

static int fail(const struct reader *r, const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	fprintf(stderr, "string: %s: offset=%zu: ", r->path, r->pos);
	vfprintf(stderr, fmt, ap);
	fputc('\n', stderr);
	va_end(ap);
	return PARSE_ERROR;
}

static int take(struct reader *r, uint64_t size, const uint8_t **out)
{
	if (size > r->len - r->pos)
		return fail(r, "数据范围越界 size=%llu file_size=%zu",
			    (unsigned long long)size, r->len);
	if (out)
		*out = r->data + r->pos;
	r->pos += size;
	return PARSE_OK;
}

static int take_array(struct reader *r, uint64_t count, size_t width,
		      const uint8_t **out)
{
	if (count > ARRAY_MAX)
		return fail(r, "数组数量异常 count=%llu",
			    (unsigned long long)count);
	return take(r, count * width, out);
}

static int take_string(struct reader *r, const uint8_t **out, size_t *len)
{
	size_t window = r->len - r->pos;
	const uint8_t *end;

	if (window > STRING_MAX)
		window = STRING_MAX;
	end = memchr(r->data + r->pos, 0, window);
	if (!end)
		return fail(r, "字符串无终止符");
	if (out)
		*out = r->data + r->pos;
	if (len)
		*len = end - (r->data + r->pos);
	r->pos += end - (r->data + r->pos) + 1;
	return PARSE_OK;
}

/* 只有 bit61 置位的指针在流中内联了字符串。 */
static int ptr_string(struct reader *r, uint64_t ptr, const uint8_t **out,
		      size_t *len)
{
	if (out)
		*out = NULL;
	if (!ptr || !(ptr & PTR_INLINE))
		return PARSE_OK;
	return take_string(r, out, len);
}

/*
 * 严格 UTF-8：拒绝过长编码、代理项和
 * 大于 U+10FFFF 的码点。
 */
static bool utf8_valid(const uint8_t *s, size_t len)
{
	size_t i = 0;

	while (i < len) {
		uint8_t c = s[i];
		size_t n;
		uint8_t lo = 0x80, hi = 0xbf;

		if (c < 0x80) {
			i++;
			continue;
		}
		if (c >= 0xc2 && c <= 0xdf) {
			n = 1;
		} else if (c >= 0xe0 && c <= 0xef) {
			n = 2;
			if (c == 0xe0)
				lo = 0xa0;
			else if (c == 0xed)
				hi = 0x9f;
		} else if (c >= 0xf0 && c <= 0xf4) {
			n = 3;
			if (c == 0xf0)
				lo = 0x90;
			else if (c == 0xf4)
				hi = 0x8f;
		} else {
			return false;
		}
		if (n > len - i - 1)
			return false;
		if (s[i + 1] < lo || s[i + 1] > hi)
			return false;
		for (size_t k = 2; k <= n; k++) {
			if (s[i + k] < 0x80 || s[i + k] > 0xbf)
				return false;
		}
		i += n + 1;
	}
	return true;
}

static int parse_localize(struct reader *r, struct package *pkg,
			  const uint8_t *hdr)
{
	uint64_t key = get_le(hdr, 8);
	uint64_t tp = get_le(hdr + 8, 8);
	uint64_t id = tp & ~PTR_INLINE;
	const uint8_t *text;
	size_t len = 0;
	struct slot *slot;
	int ret;

	ret = ptr_string(r, tp, &text, &len);
	if (ret)
		return ret;
	pkg->extracted++;
	slot = map_slot(&pkg->ids, id);
	if (text) {
		if (!utf8_valid(text, len))
			return fail(r, "本地化文本不是 UTF-8: %016llx",
				    (unsigned long long)key);
		if (slot->used && (slot->len != len ||
				   memcmp(slot->str, text, len)))
			return fail(r, "同一文本ID对应不同文本: %016llx",
				    (unsigned long long)id);
		*slot = (struct slot){ id, text, len, true };
		pkg->inlined++;
	} else {
		pkg->referenced++;
		if (!slot->used) {
			fprintf(stderr, "string: %s: 未解析引用 key=%016llx\n",
				r->path, (unsigned long long)key);
			pkg->unresolved++;
			return PARSE_OK;
		}
		text = slot->str;
		len = slot->len;
	}
	push_row(key, text, len);
	return PARSE_OK;
}

static int parse_netconst(struct reader *r, const uint8_t *hdr)
{
	uint64_t count = get_le(hdr + 20, 4);
	const uint8_t *entries;
	int ret;

	if (!get_le(hdr + 32, 8) || hdr[13] > 1)
		return PARSE_OK;
	ret = take_array(r, count, 8, &entries);
	if (ret || hdr[13])
		return ret;
	for (size_t i = 0; i < count; i++) {
		const uint8_t *s;
		size_t len;

		ret = ptr_string(r, get_le(entries + i * 8, 8), &s, &len);
		if (ret)
			return ret;
		if (s)
			push_token(s, len);
	}
	return PARSE_OK;
}

static int parse_kvp(struct reader *r, const uint8_t *hdr)
{
	uint64_t ptr = get_le(hdr + 8, 8);
	int32_t count = (int32_t)get_le(hdr + 16, 4);
	const uint8_t *entries;
	int ret;

	if (!ptr)
		return PARSE_OK;
	if (count < 0)
		return fail(r, "keyvaluepairs 数量为负");
	ret = take_array(r, count, 16, &entries);
	for (int32_t i = 0; !ret && i < count; i++)
		ret = ptr_string(r, get_le(entries + i * 16, 8), NULL, NULL);
	return ret;
}

static int parse_rawfile(struct reader *r, const uint8_t *hdr)
{
	uint64_t compressed = get_le(hdr + 12, 4);
	uint64_t raw_size = get_le(hdr + 16, 4);

	if (!get_le(hdr + 24, 8))
		return PARSE_OK;
	return take(r, compressed ? compressed : raw_size + 1, NULL);
}

static int parse_image(struct reader *r, const uint8_t *hdr)
{
	uint8_t flags = hdr[20];
	int ret = PARSE_OK;

	if ((get_le(hdr + 8, 8) & PTR_INLINE) && (flags & 0x40))
		ret = take(r, get_le(hdr + 40, 2), NULL);
	if (!ret && get_le(hdr + 48, 8))
		ret = take_array(r, hdr[45], 24, NULL);
	if (!ret && !(flags & 4) && get_le(hdr + 56, 8))
		ret = take(r, get_le(hdr + 24, 4), NULL);
	return ret;
}

static size_t header_size(uint32_t type)
{
	switch (type) {
	case TYPE_IMAGE:
		return 64;
	case TYPE_LOCALIZE:
		return 16;
	case TYPE_RAWFILE:
		return 32;
	case TYPE_NETCONST:
		return 40;
	case TYPE_KVP:
		return 24;
	default:
		return 0;
	}
}

static int parse_asset(struct reader *r, struct package *pkg, uint32_t type,
		       uint64_t ptr)
{
	uint64_t masked = ptr & PTR_FULL;
	const uint8_t *hdr;
	size_t size;
	int ret;

	if (masked != PTR_FULL) {
		if (masked == PTR_DEFAULT)
			return take_string(r, NULL, NULL);
		return PARSE_OK;
	}
	size = header_size(type);
	if (!size)
		return PARSE_UNSUPPORTED;
	ret = take(r, size, &hdr);
	if (ret)
		return ret;
	switch (type) {
	case TYPE_LOCALIZE:
		return parse_localize(r, pkg, hdr);
	case TYPE_NETCONST:
		return parse_netconst(r, hdr);
	case TYPE_RAWFILE:
		return parse_rawfile(r, hdr);
	case TYPE_KVP:
		return parse_kvp(r, hdr);
	default:
		return parse_image(r, hdr);
	}
}

/*
 * 按 XAssetList 顺序读取；遇到未实现的类型
 * 停止该包，之后的条目计为缺失。
 */
static int parse_package(struct reader *r, struct package *pkg)
{
	const uint8_t *hdr, *table = NULL;
	uint64_t nr_strings, strings, nr_assets, assets;
	int ret;

	ret = take(r, 32, &hdr);
	if (ret)
		return ret;
	nr_strings = get_le(hdr, 4);
	strings = get_le(hdr + 8, 8);
	nr_assets = get_le(hdr + 16, 4);
	assets = get_le(hdr + 24, 8);
	if (strings) {
		const uint8_t *ptrs;

		ret = take_array(r, nr_strings, 8, &ptrs);
		for (size_t i = 0; !ret && i < nr_strings; i++) {
			uint64_t ptr = get_le(ptrs + i * 8, 8);

			ret = ptr_string(r, ptr, NULL, NULL);
		}
		if (ret)
			return ret;
	}
	if (assets) {
		ret = take_array(r, nr_assets, 16, &table);
		if (ret)
			return ret;
	} else {
		nr_assets = 0;
	}
	for (size_t i = 0; i < nr_assets; i++) {
		if (get_le(table + i * 16, 4) == TYPE_LOCALIZE &&
		    (get_le(table + i * 16 + 8, 8) & PTR_FULL) == PTR_FULL)
			pkg->declared++;
	}
	map_init(&pkg->ids, pkg->declared);
	for (size_t i = 0; i < nr_assets; i++) {
		uint32_t type = (uint32_t)get_le(table + i * 16, 4);

		ret = parse_asset(r, pkg, type, get_le(table + i * 16 + 8, 8));
		if (ret == PARSE_UNSUPPORTED) {
			pkg->stopped = true;
			pkg->stop_index = i;
			pkg->stop_type = type;
			break;
		}
		if (ret)
			break;
	}
	map_free(&pkg->ids);
	if (ret == PARSE_ERROR)
		return ret;
	if (!pkg->stopped && r->pos != r->len)
		return fail(r, "FF未精确消费到EOF");
	return PARSE_OK;
}

/*
 * sub_1718510：反斜杠转 '/'、合并连续 '/'、
 * 小写，逐字节乘 FNV 质数，每轮清除最高位。
 * 非 ASCII 候选不参与。
 */
static bool path_hash(const uint8_t *s, size_t len, uint64_t *out)
{
	uint64_t v = 0x47f5817a5ef961baULL;
	uint8_t prev = 0;

	for (size_t i = 0; i < len; i++) {
		uint8_t c = s[i];

		if (c >= 0x80)
			return false;
		if (c == '\\')
			c = '/';
		if (c == '/' && prev == '/')
			continue;
		prev = c;
		if (c >= 'A' && c <= 'Z')
			c += 'a' - 'A';
		v = ((v & PTR_FULL) ^ c) * 0x100000001b3ULL;
	}
	*out = v & PTR_FULL;
	return true;
}

/* 同 key 多个拼写时保留字节序最小者。 */
static void offer_name(const uint8_t *s, size_t len)
{
	struct slot *slot;
	uint64_t key;
	size_t n;
	int cmp;
	uint8_t *copy;

	if (!path_hash(s, len, &key))
		return;
	slot = map_slot(&key_names, key);
	if (!slot->used)
		return;
	if (slot->str) {
		n = slot->len < len ? slot->len : len;
		cmp = memcmp(s, slot->str, n);
		if (cmp > 0 || (!cmp && len >= slot->len))
			return;
		free((void *)slot->str);
	}
	copy = malloc(len);
	if (!copy)
		die("内存不足");
	memcpy(copy, s, len);
	slot->str = copy;
	slot->len = len;
}

static bool name_head(uint8_t c)
{
	return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') ||
	       (c >= 'a' && c <= 'z') || c == '_';
}

static bool name_body(uint8_t c)
{
	return name_head(c) || c == '.' || c == '/' || c == '-';
}

/* 等价于正则 [A-Za-z0-9_][A-Za-z0-9_./-]{1,200} 的不重叠匹配。 */
static void scan_names(const uint8_t *data, size_t len)
{
	size_t i = 0;

	while (i < len) {
		size_t n = 1;

		if (!name_head(data[i])) {
			i++;
			continue;
		}
		while (n < NAME_TOKEN_MAX && i + n < len &&
		       name_body(data[i + n]))
			n++;
		if (n >= 2)
			offer_name(data + i, n);
		i += n;
	}
}

static const uint8_t *map_file(const char *path, size_t *len)
{
	struct stat st;
	void *data;
	int fd;

	fd = open(path, O_RDONLY | O_CLOEXEC);
	if (fd < 0)
		die("%s: %s", path, strerror(errno));
	if (fstat(fd, &st))
		die("%s: %s", path, strerror(errno));
	*len = st.st_size;
	if (!*len) {
		close(fd);
		return (const uint8_t *)"";
	}
	data = mmap(NULL, *len, PROT_READ, MAP_PRIVATE, fd, 0);
	if (data == MAP_FAILED)
		die("%s: %s", path, strerror(errno));
	close(fd);
	return data;
}

static int scan_name_file(const char *path, const struct stat *st, int flag,
			  struct FTW *ftw)
{
	const uint8_t *data;
	size_t len;

	(void)ftw;
	if (flag != FTW_F || !S_ISREG(st->st_mode))
		return 0;
	data = map_file(path, &len);
	scan_names(data, len);
	if (len)
		munmap((void *)data, len);
	name_files++;
	return 0;
}

static int row_cmp(const void *a, const void *b)
{
	const struct row *x = a, *y = b;
	size_t n = x->len < y->len ? x->len : y->len;
	int cmp;

	if (x->key != y->key)
		return x->key < y->key ? -1 : 1;
	cmp = n ? memcmp(x->text, y->text, n) : 0;
	if (cmp)
		return cmp;
	return (x->len > y->len) - (x->len < y->len);
}

static bool row_same(const struct row *x, const struct row *y)
{
	return x->key == y->key && x->len == y->len &&
	       (!x->len || !memcmp(x->text, y->text, x->len));
}

static void put_field(FILE *out, const uint8_t *s, size_t len)
{
	for (size_t i = 0; i < len; i++) {
		switch (s[i]) {
		case '\\':
			fputs("\\\\", out);
			break;
		case '\t':
			fputs("\\t", out);
			break;
		case '\n':
			fputs("\\n", out);
			break;
		case '\r':
			fputs("\\r", out);
			break;
		default:
			fputc(s[i], out);
		}
	}
}

/* O_EXCL 创建，失败时删除半成品。 */
static void write_tsv(const char *path)
{
	FILE *out;
	bool bad;
	int fd;

	fd = open(path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0644);
	if (fd < 0)
		die("%s: %s", path, strerror(errno));
	out = fdopen(fd, "w");
	if (!out)
		die("%s: %s", path, strerror(errno));
	fputs("key\tname\ttext\n", out);
	for (size_t i = 0; i < nr_rows; i++) {
		struct slot *slot = map_slot(&key_names, rows[i].key);

		fprintf(out, "%016llx\t", (unsigned long long)rows[i].key);
		put_field(out, slot->str, slot->str ? slot->len : 0);
		fputc('\t', out);
		put_field(out, rows[i].text, rows[i].len);
		fputc('\n', out);
	}
	bad = ferror(out);
	if (fclose(out))
		bad = true;
	if (bad) {
		unlink(path);
		die("%s: 写入失败", path);
	}
}

static size_t count_named(void)
{
	size_t n = 0;

	for (size_t i = 0; i <= key_names.mask; i++) {
		if (key_names.slots[i].used && key_names.slots[i].str)
			n++;
	}
	return n;
}

static void usage(FILE *out)
{
	fputs("用法: string -o OUTPUT.tsv [-n NAMES]... FF.decoded.bin...\n"
	      "  -o  输出 TSV，须尚不存在\n"
	      "  -n  名称候选文件或目录，可重复\n"
	      "退出码：0 全部完整，1 有包停止或引用未解析，2 错误（不写输出）\n",
	      out);
}

/* 去重后统计唯一 key，并建立 key -> 名称表。 */
static size_t dedupe_rows(size_t *multi)
{
	size_t keys = 0, n = 0;

	if (nr_rows)
		qsort(rows, nr_rows, sizeof(*rows), row_cmp);
	for (size_t i = 0; i < nr_rows; i++) {
		if (!n || !row_same(&rows[n - 1], &rows[i]))
			rows[n++] = rows[i];
	}
	nr_rows = n;
	*multi = 0;
	for (size_t i = 0; i < nr_rows; i++) {
		if (i && rows[i].key == rows[i - 1].key) {
			if (i < 2 || rows[i - 2].key != rows[i].key)
				(*multi)++;
			continue;
		}
		keys++;
	}
	map_init(&key_names, keys);
	for (size_t i = 0; i < nr_rows; i++) {
		struct slot *slot = map_slot(&key_names, rows[i].key);

		slot->key = rows[i].key;
		slot->used = true;
	}
	return keys;
}

int main(int argc, char **argv)
{
	const char *output = NULL;
	char **names;
	size_t nr_names = 0, keys, multi;
	size_t declared = 0, extracted = 0, unresolved = 0, complete = 0;
	struct stat st;
	int opt;

	names = calloc(argc, sizeof(*names));
	if (!names)
		die("内存不足");
	while ((opt = getopt(argc, argv, "o:n:h")) != -1) {
		switch (opt) {
		case 'o':
			output = optarg;
			break;
		case 'n':
			names[nr_names++] = optarg;
			break;
		case 'h':
			usage(stdout);
			return 0;
		default:
			usage(stderr);
			return 2;
		}
	}
	if (!output || optind == argc) {
		usage(stderr);
		return 2;
	}
	if (!lstat(output, &st))
		die("%s: 输出已存在", output);
	for (int i = optind; i < argc; i++) {
		struct package pkg = { 0 };
		struct reader r = { .path = argv[i] };

		r.data = map_file(argv[i], &r.len);
		if (parse_package(&r, &pkg))
			return 2;
		declared += pkg.declared;
		extracted += pkg.extracted;
		unresolved += pkg.unresolved;
		if (pkg.declared == pkg.extracted && !pkg.unresolved) {
			complete++;
			continue;
		}
		fprintf(stderr, "INCOMPLETE %s", argv[i]);
		fprintf(stderr, " declared=%zu extracted=%zu unresolved=%zu",
			pkg.declared, pkg.extracted, pkg.unresolved);
		if (pkg.stopped)
			fprintf(stderr, " stop_index=%zu stop_type=%u",
				pkg.stop_index, pkg.stop_type);
		fputc('\n', stderr);
	}
	keys = dedupe_rows(&multi);
	for (size_t i = 0; i < nr_tokens; i++)
		offer_name(tokens[i].str, tokens[i].len);
	for (size_t i = 0; i < nr_names; i++) {
		if (stat(names[i], &st))
			die("%s: %s", names[i], strerror(errno));
		if (S_ISDIR(st.st_mode)) {
			if (nftw(names[i], scan_name_file, 64, FTW_PHYS))
				die("%s: 遍历失败", names[i]);
		} else {
			scan_name_file(names[i], &st, FTW_F, NULL);
		}
	}
	write_tsv(output);
	printf("RESULT packages=%d complete=%zu declared=%zu extracted=%zu",
	       argc - optind, complete, declared, extracted);
	printf(" unresolved=%zu keys=%zu rows=%zu multi_text_keys=%zu",
	       unresolved, keys, nr_rows, multi);
	printf(" named=%zu name_files=%zu\n", count_named(), name_files);
	return complete == (size_t)(argc - optind) ? 0 : 1;
}
