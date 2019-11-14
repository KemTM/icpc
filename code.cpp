#include <algorithm>
#include <bitset>
#include <cassert>
#include <cfloat>
#include <chrono>
#include <climits>
#include <cmath>
#include <complex>
#include <cstring>
#include <functional>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <list>
#include <map>
#include <memory>
#include <queue>
#include <random>
#include <set>
#include <stack>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#define tg(i, t) std::get<i>(t)
#define complain *(int *)0 = 0

#ifndef _DEBUG
#define cerr  \
    if (true) \
    {         \
    }         \
    else      \
        cerr
#endif

using namespace std;

typedef long long ll;
typedef __int128_t lll;
typedef pair<string, int> si;
typedef pair<int, int> ii;
typedef tuple<int, int, int> iii;
typedef pair<ll, ll> pll;
ll MOD = 1000000007;
const double eps = 1e-8;
constexpr ll linf = numeric_limits<ll>::max();
constexpr int inf = numeric_limits<int>::max();
const double PI = 3.141592653589793238462643383279502884197;

/*******************
 * HERE BE DRAGONS *
 *******************/

bool equals(double a, double b)
{
    return abs(a - b) < eps;
}

bool lt(double a, double b)
{
    return a < b && !equals(a, b);
}

bool lte(double a, double b)
{
    return a < b || equals(a, b);
}

bool gte(double a, double b)
{
    return a > b || equals(a, b);
}

bool gt(double a, double b)
{
    return a > b && !equals(a, b);
}

inline double clamp(const double &min, const double &max, const double &val)
{
    if (val < min)
        return min;
    if (val > max)
        return max;
    return val;
}

ll madd(ll a, ll b)
{
    return (a + b) % MOD;
}

ll mmul(ll a, ll b)
{
    return (a * b) % MOD;
}

ll msub(ll a, ll b)
{
    ll ans = (a - b) % MOD;
    while (ans < 0)
        ans += MOD;
    return ans;
}

ll mpow(ll base, ll exp)
{
    if (exp == 0LL)
        return 1LL;
    if (exp == 1LL)
        return base % MOD;
    ll e = mpow(base, exp / 2L);
    ll a = mmul(e, e);
    if (exp % 2 == 1)
        a = mmul(a, base);
    return a;
}

ll mdiv(ll a, ll b)
{
    ll inv = mpow(b, MOD - 2);
    return mmul(a, inv);
}

ll pow(ll base, ll exp)
{
    if (exp == 1)
        return base;

    ll e = pow(base, exp / 2);

    return e * e * (exp % 2 ? base : 1);
}

template <typename T>
T gcd(T a, T b)
{
    return (b ? gcd(b, a % b) : a);
}

struct vec2
{
    double x, y;
    int index;

    vec2() : vec2(0, 0, -1) {}
    vec2(double x, double y, int index = -1) : x{x}, y{y}, index{index} {}

    inline vec2 operator-(const vec2 &other) const
    {
        return vec2(x - other.x, y - other.y);
    }

    inline vec2 operator+(const vec2 &other) const
    {
        return vec2(x + other.x, y + other.y);
    }

    inline double operator*(const vec2 &other) const
    {
        return x * other.x + y * other.y;
    }

    inline vec2 operator*(const double scalar) const
    {
        return vec2(x * scalar, y * scalar);
    }

    inline bool operator==(const vec2 &v2) const
    {
        return equals(this->x, v2.x) && equals(this->y, v2.y);
    }

    inline bool operator<(const vec2 &other) const
    {
        return equals(y, other.y) ? lt(x, other.x) : lt(y, other.y);
        //return equals(x, other.x) ? lt(y, other.y) : lt(x, other.x);
    }

    inline double angle(const vec2 &other) const
    {
        return acos((*this * other) / (length() * other.length()));
    }

    inline double crossMod(const vec2 &other) const
    {
        return x * other.y - y * other.x;
    }

    inline double length_squared() const
    {
        return x * x + y * y;
    }

    inline double length() const
    {
        return sqrt(length_squared());
    }

    void norm()
    {
        double l = length();
        x /= l;
        y /= l;
    }

    void rotate(double angle)
    {
        double l = length();

        double phi = acos(x / l);

        x = l * cos(phi + angle);
        y = l * sin(phi + angle);
    }

    inline double angleToOX() const
    {
        auto oXVec = vec2(1, 0);
        return oXVec.angle(*this);
    }
};

inline double dist_squared(vec2 v, vec2 w)
{
    return (v.x - w.x) * (v.x - w.x) + (v.y - w.y) * (v.y - w.y);
}

inline double distance(vec2 v, vec2 w)
{
    return sqrt(dist_squared(v, w));
}

double minimum_distance(vec2 v, vec2 w, vec2 p)
{
    vec2 ttt = (w - v);
    // Return minimum distance between line segment vw and point p
    const double l2 = ttt.length_squared(); // i.e. |w-v|^2 -  avoid a sqrt
    if (equals(l2, 0))
        return dist_squared(p, v); // v == w case
                                   // Consider the line extending the segment, parameterized as v + t (w - v).
                                   // We find projection of point p onto the line.
                                   // It falls where t = [(p-v) . (w-v)] / |w-v|^2
                                   // We clamp t from [0,1] to handle points outside the segment vw.
    const double tt = (p - v) * ttt / l2;
    const double t = clamp(0.0, 1.0, tt);
    const vec2 projection = v + ttt * t; // Projection falls on the segment
    return dist_squared(p, projection);
}

// Templated Segment Tree, should support any type you need
template <class Type, int Size, class Worst, class Combine>
struct segment_tree
{
    Type data[4 * Size];
    vector<Type> vals;
    int maxPos = 0;

    Worst w;
    Combine c;

    segment_tree()
    {
        fill(data, data + 4 * Size, w());
    }

    segment_tree(vector<Type> vals) : vals(vals)
    {
        fill(data, data + Size, w());
        build(0, 0, vals.size() - 1);
    }

    Type build(int pos, int startIdx, int endIdx)
    {
        if (startIdx == endIdx)
        {
            data[pos] = vals[startIdx];
        }
        else
        {
            int mid = (startIdx + endIdx) / 2;
            data[pos] = c(build(2 * pos + 1, startIdx, mid), build(2 * pos + 2, mid + 1, endIdx));
        }

        maxPos = max(maxPos, pos);

        return data[pos];
    }

    Type set(Type val, int idx, int pos = 0, int startIdx = 0, int endIdx = Size - 1)
    {
        if (idx > endIdx || idx < startIdx)
        {
            return data[pos];
        }
        else if (startIdx == endIdx)
        {
            data[pos] = val;
            return data[pos];
        }

        int mid = (startIdx + endIdx) / 2;

        data[pos] = c(set(val, idx, 2 * pos + 1, startIdx, mid), set(val, idx, 2 * pos + 2, mid + 1, endIdx));

        return data[pos];
    }

    Type query(int l, int r, int pos = 0, int startIdx = 0, int endIdx = Size - 1)
    {
        if (l > endIdx || r < startIdx)
        {
            return w();
        }
        else if (startIdx == endIdx)
        {
            return data[pos];
        }
        else if (l <= startIdx && r >= endIdx)
        {
            return data[pos];
        }

        int mid = (startIdx + endIdx) / 2;

        return c(query(l, r, 2 * pos + 1, startIdx, mid), query(l, r, 2 * pos + 2, mid + 1, endIdx));
    }
};

// TODO: cleanup
struct trie
{
private:
    struct node
    {
        static int count;
        int id;
        vector<int> terminal;
        char enter;
        node *next[30];
        node *parent;
        node *suffix;
        vector<node *> suffixReverse;
        node *superSuffix;
        vector<node *> superSuffixReverse;

        node(node *parent = nullptr, char enter = 0, vector<int> terminal = {}) : terminal(terminal),
                                                                                  enter(enter),
                                                                                  parent(parent),
                                                                                  suffix(nullptr),
                                                                                  superSuffix(nullptr)
        {
            id = count++;
            fill(next, next + 30, nullptr);
        }
    };

    char from, to;
    node *root;
    vector<string> patterns;

public:
    trie(char from, char to) : from(from), to(to)
    {
        root = new node();
    }

    int insert(const string &pattern)
    {
        node *cur = root;

        for (int i = 0; i < pattern.length(); i++)
        {
            char c = pattern[i];
            int c_idx = c - from;

            if (cur->next[c_idx] == nullptr)
            {
                cur->next[c_idx] = new node(cur, c);
            }

            if (i + 1 == pattern.length())
            {
                cur->next[c_idx]->terminal.push_back(patterns.size());
            }

            cur = cur->next[c_idx];
        }

        patterns.push_back(pattern);

        return patterns.size() - 1;
    }

    void make_automaton()
    {
        queue<node *> Q;

        Q.push(root);

        while (!Q.empty())
        {
            node *cur = Q.front();
            Q.pop();

            for (const auto &n : cur->next)
            {
                if (n != nullptr)
                    Q.push(n);
            }

            if (cur == root) // root
            {
                // nothing to do
            }
            else if (cur->parent == root) // level 1
            {
                cur->suffix = root;
                cur->superSuffix = root;

                root->suffixReverse.push_back(cur);
                root->superSuffixReverse.push_back(cur);
            }
            else // proceed normally
            {
                int enter_idx = cur->enter - from;

                cur->suffix = cur->parent->suffix->next[enter_idx];

                cur->parent->suffix->next[enter_idx]->suffixReverse.push_back(cur);

                if (cur->suffix == root)
                {
                    cur->superSuffix = root;
                    root->superSuffixReverse.push_back(cur);
                }
                else
                {
                    if (cur->suffix->terminal.empty())
                    {
                        cur->superSuffix = cur->suffix->superSuffix;
                        cur->suffix->superSuffix->superSuffixReverse.push_back(cur);
                    }
                    else
                    {
                        cur->superSuffix = cur->suffix;
                        cur->suffix->superSuffixReverse.push_back(cur);
                    }
                }
            }

            for (char c = from; c <= to; c++)
            {
                int c_idx = c - from;

                if (cur->next[c_idx] == nullptr)
                {
                    if (cur == root)
                    {
                        cur->next[c_idx] = root;
                    }
                    else
                    {
                        cur->next[c_idx] = cur->suffix->next[c_idx];
                    }
                }
            }
        }
    }

    vector<int> apply(const string &text)
    {
        vector<int> result(patterns.size());

        vector<int> visits(node::count);

        node *cur = root;

        for (auto &c : text)
        {
            int c_idx = c - from;

            cur = cur->next[c_idx];

            visits[cur->id]++;
        }

        function<int(node *)> dfs = [&](node *u) {
            int ans = visits[u->id];

            for (node *n : u->superSuffixReverse)
            {
                ans += dfs(n);
            }

            for (auto pattern : u->terminal)
            {
                result[pattern] = ans;
            }

            return ans;
        };

        dfs(root);

        return result;
    }

    bool solve()
    {
        vector<int> visited(node::count, -1);

        function<void(node *)> dfs1 = [&](node *u) {
            if (u != root)
            {
                if (visited[u->suffix->id] == 1 || !u->terminal.empty())
                    visited[u->id] = 1;
            }

            for (node *n : u->suffixReverse)
            {
                dfs1(n);
            }
        };

        dfs1(root);

        function<bool(node *)> dfs2 = [&](node *u) {
            visited[u->id] = 0;

            bool ans = false;

            for (node *n : u->next)
            {
                if (n == nullptr)
                    continue;

                if (visited[n->id] == 0)
                    return true;
                else if (visited[n->id] == -1)
                    ans |= dfs2(n);
            }

            visited[u->id] = 1;

            return ans;
        };

        return dfs2(root);
    }

    // For debugging purposes
    // WARNING: MAY GENERATE A CRAPTON OF OUTPUT. DO NOT USE IN PRODUCTION.
    friend ostream &
    operator<<(ostream &out, trie &trie)
    {
        out << "NODES: " << node::count << "\n"
            << "PATTERNS: " << trie.patterns.size() << "\n";

        for (int i = 0; i < trie.patterns.size(); i++)
        {
            out << i + 1 << ") " << trie.patterns[i] << '\n';
        }

        out << '\n';

        queue<node *> Q;

        map<node *, int> ids, visited;
        ids[nullptr] = -1;

        Q.push(trie.root);

        visited[trie.root] = true;

        while (!Q.empty())
        {
            node *cur = Q.front();
            Q.pop();

            ids[cur] = cur->id;

            out << "[NODE " << cur->id << "]\n"
                << "Terminals: ";

            for (auto pattern : cur->terminal)
            {
                out << pattern << " ";
            }

            out << "| Enter: " << ((cur->enter >= trie.from && cur->enter <= trie.to) ? cur->enter : '-') << " | Parent: " << ids[cur->parent] << " | SL: " << ids[cur->suffix] << " | SSL: " << ids[cur->superSuffix] << "\n"
                << "Edges:\n";

            for (char c = trie.from; c <= trie.to; c++)
            {
                int c_idx = c - trie.from;

                out << c << " -> " << cur->next[c_idx]->id << '\n';

                if (!visited[cur->next[c_idx]])
                {
                    visited[cur->next[c_idx]] = true;
                    Q.push(cur->next[c_idx]);
                }
            }

            out << '\n';
        }

        return out;
    }
};

int trie::node::count = 0;

tuple<ll, ll, ll> EXGCD(ll a, ll b)
{
    if (b == 0)
        return {1, 0, a};
    auto inter = EXGCD(b, a % b);

    return {get<1>(inter), get<0>(inter) - get<1>(inter) * (a / b), get<2>(inter)};
}

template <size_t Size>
struct binomial
{
private:
    vector<vector<ll>> data;

public:
    binomial(bool modulo = true)
    {
        assert(Size > 0);

        data.resize(Size + 1);

        for (auto &row : data)
        {
            row.resize(Size + 1);
            row[0] = 1;
        }

        for (int i = 1; i <= Size; i++)
        {
            for (int j = 1; j <= i; j++)
            {
                if (modulo)
                    data[i][j] = madd(data[i - 1][j], data[i - 1][j - 1]);
                else
                    data[i][j] = data[i - 1][j] + data[i - 1][j - 1];
            }
        }
    }

    vector<ll> &operator[](int idx)
    {
        return data[idx];
    }

    auto begin()
    {
        return data.begin();
    }

    auto end()
    {
        return data.end();
    }

    friend ostream &operator<<(ostream &out, const binomial &bin)
    {
        for (int i = 0; i < bin.data.size(); i++)
        {
            for (int j = 0; j <= i; j++)
            {
                out << bin.data[i][j] << " ";
            }
            out << "\n";
        }

        return out;
    }
};

/********************
 * HERE DRAGONS END *
 ********************/
const int MAXN = 1000010;

ll counts[MAXN];
ll a[MAXN], b[MAXN];
// ll pow2s[MAXN];

int main()
{
    ios_base::sync_with_stdio(false);
    cin.tie(0);
    cout.tie(0);
    cerr.tie(0);
#ifdef _DEBUG
#ifndef HIGHTAIL
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    freopen("debug.txt", "w", stderr);
#endif // HIGHTAIL
#endif // _DEBUG
}