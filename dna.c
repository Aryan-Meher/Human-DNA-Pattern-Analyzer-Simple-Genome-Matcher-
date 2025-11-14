#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAX_SEQ_LEN 2000
#define MAX_SEQS 200
#define ALPHABET 4

/* ---------- Utility: map base to index ---------- */
int base_index(char b) {
    b = toupper(b);
    if (b == 'A') return 0;
    if (b == 'C') return 1;
    if (b == 'G') return 2;
    if (b == 'T') return 3;
    return -1;
}

/* ---------- TRIE ---------- */
typedef struct TrieNode {
    struct TrieNode* child[ALPHABET];
    int endOfSeq;
    int seqIndex;
} TrieNode;

TrieNode* createTrieNode() {
    TrieNode* node = (TrieNode*) malloc(sizeof(TrieNode));
    int i;
    for (i = 0; i < ALPHABET; i++)
        node->child[i] = NULL;
    node->endOfSeq = 0;
    node->seqIndex = 0;
    return node;
}

void trieInsert(TrieNode* root, const char* seq, int index) {
    TrieNode* cur = root;
    int i;
    for (i = 0; seq[i]; i++) {
        int idx = base_index(seq[i]);
        if (idx < 0) continue;
        if (!cur->child[idx])
            cur->child[idx] = createTrieNode();
        cur = cur->child[idx];
    }
    cur->endOfSeq = 1;
    cur->seqIndex = index;
}

int trieSearch(TrieNode* root, const char* seq) {
    TrieNode* cur = root;
    int i;
    for (i = 0; seq[i]; i++) {
        int idx = base_index(seq[i]);
        if (idx < 0) return 0;
        if (!cur->child[idx]) return 0;
        cur = cur->child[idx];
    }
    return cur->endOfSeq;
}

/* ---------- Sequence storage ---------- */
char *sequences[MAX_SEQS + 1];
int seqCount = 0;

/* ---------- Queue for match results ---------- */
typedef struct MatchNode {
    int seqIndex;
    int position;
    struct MatchNode* next;
} MatchNode;

typedef struct {
    MatchNode* head;
    MatchNode* tail;
    int size;
} MatchQueue;

void initQueue(MatchQueue* q) {
    q->head = q->tail = NULL;
    q->size = 0;
}

void enqueue(MatchQueue* q, int seqIndex, int position) {
    MatchNode* n = (MatchNode*) malloc(sizeof(MatchNode));
    n->seqIndex = seqIndex;
    n->position = position;
    n->next = NULL;

    if (!q->tail)
        q->head = q->tail = n;
    else {
        q->tail->next = n;
        q->tail = n;
    }
    q->size++;
}

MatchNode* dequeue(MatchQueue* q) {
    MatchNode* n;
    if (!q->head) return NULL;
    n = q->head;
    q->head = q->head->next;
    if (!q->head) q->tail = NULL;
    q->size--;
    return n;
}

/* ---------- KMP ---------- */
int* kmpPrefix(const char* pat) {
    int m = strlen(pat);
    int* lps = (int*) malloc(sizeof(int) * m);
    int i, len;

    lps[0] = 0;
    len = 0;

    for (i = 1; i < m; i++) {
        while (len > 0 && pat[i] != pat[len])
            len = lps[len - 1];
        if (pat[i] == pat[len])
            len++;
        lps[i] = len;
    }
    return lps;
}

void kmpSearch(const char* text, const char* pat, int seqIndex, MatchQueue* q) {
    int n = strlen(text);
    int m = strlen(pat);
    int* lps = kmpPrefix(pat);
    int i = 0, j = 0;

    while (i < n) {
        if (text[i] == pat[j]) {
            i++; j++;
        }
        if (j == m) {
            enqueue(q, seqIndex, i - j);
            j = lps[j - 1];
        }
        else if (i < n && text[i] != pat[j]) {
            if (j != 0) j = lps[j - 1];
            else i++;
        }
    }
    free(lps);
}

/* ---------- Suffix array + LCP ---------- */
typedef struct {
    const char* s;
    int offset;
} Suffix;

int suffix_cmp(const void* a, const void* b) {
    Suffix* sa = (Suffix*) a;
    Suffix* sb = (Suffix*) b;
    return strcmp(sa->s + sa->offset, sb->s + sb->offset);
}

int lcp(const char* s, int i, int j) {
    int k = 0;
    while (s[i + k] && s[j + k] && s[i + k] == s[j + k])
        k++;
    return k;
}

int findLongestRepeatedSubstring(const char* s, char* outbuf, int outsz) {
    int n = strlen(s);
    int i;
    Suffix* arr = (Suffix*) malloc(sizeof(Suffix) * n);
    int best = 0, bestpos = -1;

    for (i = 0; i < n; i++) {
        arr[i].s = s;
        arr[i].offset = i;
    }

    qsort(arr, n, sizeof(Suffix), suffix_cmp);

    for (i = 1; i < n; i++) {
        int x = lcp(s, arr[i-1].offset, arr[i].offset);
        if (x > best) {
            best = x;
            bestpos = arr[i].offset;
        }
    }

    if (best > 0) {
        int copylen = (best < outsz - 1) ? best : outsz - 1;
        strncpy(outbuf, s + bestpos, copylen);
        outbuf[copylen] = '\0';
    } else {
        outbuf[0] = '\0';
    }

    free(arr);
    return best;
}

/* ---------- Levenshtein DP ---------- */
typedef struct {
    int subs, ins, del;
    int dist;
} EditResult;

EditResult levenshtein(const char* a, const char* b) {
    int n = strlen(a);
    int m = strlen(b);
    int i, j;

    int** dp = (int**) malloc((n+1) * sizeof(int*));
    for (i = 0; i <= n; i++)
        dp[i] = (int*) malloc((m+1) * sizeof(int));

    for (i = 0; i <= n; i++) dp[i][0] = i;
    for (j = 0; j <= m; j++) dp[0][j] = j;

    for (i = 1; i <= n; i++) {
        for (j = 1; j <= m; j++) {
            int cost = (a[i-1] == b[j-1]) ? 0 : 1;
            int del = dp[i-1][j] + 1;
            int ins = dp[i][j-1] + 1;
            int sub = dp[i-1][j-1] + cost;

            int best = del;
            if (ins < best) best = ins;
            if (sub < best) best = sub;

            dp[i][j] = best;
        }
    }

    /* Backtrace */
    int subs = 0, ins = 0, delc = 0;
    i = n; j = m;

    while (i > 0 || j > 0) {
        if (i > 0 && j > 0 &&
            dp[i][j] == dp[i-1][j-1] + (a[i-1] != b[j-1])) {
            if (a[i-1] != b[j-1]) subs++;
            i--; j--;
        }
        else if (i > 0 && dp[i][j] == dp[i-1][j] + 1) {
            delc++; i--;
        }
        else if (j > 0 && dp[i][j] == dp[i][j-1] + 1) {
            ins++; j--;
        }
        else break;
    }

    EditResult r;
    r.subs = subs;
    r.ins = ins;
    r.del = delc;
    r.dist = dp[n][m];

    for (i = 0; i <= n; i++) free(dp[i]);
    free(dp);

    return r;
}

/* ---------- Helper ---------- */
void readLine(char* buf, int size) {
    fgets(buf, size, stdin);
    buf[strcspn(buf, "\n")] = '\0';
}

void cleanDNA(char* s) {
    int i, j = 0;
    for (i = 0; s[i]; i++) {
        char c = toupper(s[i]);
        if (c=='A'||c=='C'||c=='G'||c=='T')
            s[j++] = c;
    }
    s[j] = '\0';
}

/* ---------- Main Menu ---------- */
int main() {
    TrieNode* root = createTrieNode();
    int choice;

    while (1) {
        printf("\n1. Add sequence\n2. List\n3. Search pattern\n4. Mutation check\n5. Repeats\n6. Exit\n> ");
        scanf("%d", &choice);
        getchar();

        if (choice == 1) {
            char buf[MAX_SEQ_LEN];
            printf("Enter DNA: ");
            readLine(buf, sizeof(buf));
            cleanDNA(buf);

            seqCount++;
            sequences[seqCount] = strdup(buf);
            trieInsert(root, buf, seqCount);
            printf("Stored #%d\n", seqCount);
        }

        else if (choice == 2) {
            int i;
            for (i = 1; i <= seqCount; i++)
                printf("%d: %s\n", i, sequences[i]);
        }

        else if (choice == 3) {
            char pat[MAX_SEQ_LEN];
            printf("Pattern: ");
            readLine(pat, sizeof(pat));
            cleanDNA(pat);

            MatchQueue q;
            initQueue(&q);

            int i;
            for (i = 1; i <= seqCount; i++)
                kmpSearch(sequences[i], pat, i, &q);

            if (q.size == 0)
                printf("Not found.\n");
            else {
                MatchNode* n;
                while ((n = dequeue(&q)) != NULL) {
                    printf("Sequence %d at %d\n", n->seqIndex, n->position);
                    free(n);
                }
            }
        }

        else if (choice == 4) {
            char a[MAX_SEQ_LEN], b[MAX_SEQ_LEN];
            printf("A: "); readLine(a, sizeof(a)); cleanDNA(a);
            printf("B: "); readLine(b, sizeof(b)); cleanDNA(b);

            EditResult r = levenshtein(a, b);
            printf("Distance = %d, Subs=%d Ins=%d Del=%d\n",
                   r.dist, r.subs, r.ins, r.del);
        }

        else if (choice == 5) {
            int i;
            for (i = 1; i <= seqCount; i++) {
                char out[200];
                int len = findLongestRepeatedSubstring(sequences[i], out, sizeof(out));
                if (len > 0)
                    printf("Seq %d LRS = %s (%d)\n", i, out, len);
                else
                    printf("Seq %d: no repeats\n", i);
            }
        }

        else if (choice == 6) break;
    }
    return 0;
}

