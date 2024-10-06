#include <bits/stdc++.h>
#define MAX_SIZE 1000111
using namespace std;


struct closure {
    int cnt;
    vector<int> level;
    map<set<int>, vector<int>> depset;
    // map the existential/universal variable to the tree node id
    map<int, int> var2id;
    // the dfs order of the i-th depset in the tree
    vector<int> id;
    // the subtree size of the i-th depset in the tree
    vector<int> sz; 
    // the adjacency list tree representation
    vector<vector<int>> g;
    // the i-th depset
    vector<set<int>> order;
    
    set<int> univ;

    vector<vector<int>> node_level;
    vector<vector<int>> univ_level;
    vector<vector<int>> exist_level;

    void find_closure() {
        vector<set<int>> ss;
        int i, j;
        for (auto &iter : depset) {
            ss.push_back(iter.first);
            for (auto &u : iter.first) {
                univ.insert(u);
            }
        }

        for (i = 0 ; i < (int) ss.size(); ++i) {
            for (j = i + 1; j < (int) ss.size(); ++j) {
                set<int> nset;
                for (auto &v : ss[i]) {
                    if (ss[j].find(v) != ss[j].end()) nset.insert(v);
                }

                if (depset.find(nset) == depset.end()) depset[nset] = vector<int>();           
            }
        }
    }

    void dfs(int v, int p) {
        id[v] = cnt++;
        level[v] = level[p] + 1;
        sz[v] = 1;
        if (depset.find(order[v]) != depset.end()) {
            for (auto &exist : depset[order[v]]) {
                var2id[exist] = v;
            }
        }

        for (auto &u : order[v]) {
            if (order[p].find(u) == order[p].end()) {
                var2id[u] = v;
            }
        }

        for (auto &nv : g[v]) {
            dfs(nv, v);
            sz[v] += sz[nv];
        }
    }
    // construct the closure tree from the depset
    void construct_closure_tree() {
        int i, j;
        auto cmp = [](set<int> &v1, set<int> &v2) ->bool {
            return v1.size() < v2.size();
        };

        auto issubset = [](set<int> &s, set<int> &t) -> bool {
            for (auto &v : s) {
                if (t.find(v) == t.end()) return false;
            }

            return true;
        };

        order.clear();
        order.push_back(set<int>());
        for (auto &ss : depset) {
            order.push_back(ss.first);
        }

        sort(order.begin(), order.end(), cmp);

        g = vector<vector<int>>(depset.size() + 1, vector<int>());
        level = vector<int>(depset.size() + 1, 0);
        id = vector<int>(depset.size() + 1, 0);
        sz = vector<int>(depset.size() + 1, 0);
        for (i = 2 ; i < (int) order.size(); ++i) {
            for (j = i - 1; i >= 1; --j) {
                if (issubset(order[j], order[i])) {
                    g[j].push_back(i);
                    break;
                }
            }
        }

        cnt = 1;
        dfs(1, 0);

        univ_level = vector<vector<int>>(*max_element(level.begin(), level.end()) + 1, vector<int>());
        node_level = vector<vector<int>>(*max_element(level.begin(), level.end()) + 1, vector<int>());
        exist_level = vector<vector<int>>(*max_element(level.begin(), level.end()) + 1, vector<int>());
        for (auto &iter : var2id) {
            int v = iter.first, i = iter.second;
            if (univ.find(v) == univ.end()) {
                exist_level[level[i]].push_back(v);
            } else {
                univ_level[level[i]].push_back(v);
            }
        }

        for (i = 1; i < (int) id.size(); ++i) {
            node_level[level[i]].push_back(i);
        }
    }

    void show() {
        int i;
        for (i = 1; i < (int) g.size(); ++i) {
            printf("%d: ", i);
            for (auto &c : g[i]) {
                printf("%d->", c);
            }
            printf("X\n");
        }

        for (i = 1; i < (int) order.size(); ++i) {
            printf("depset[%d]: ", i);
            for (auto &s : order[i]) {
                printf("%d ", s);
            }
            printf("\n");
        }

        for (i = 1; i < (int) id.size(); ++i) {
            printf("id[%d]=%d sz[%d]=%d level[%d]=%d\n", i, id[i], i, sz[i], i, level[i]);
        }

        for (auto &iter : var2id) {
            printf("var2id[%d]=%d\n", iter.first, iter.second);
        }

        for (i = 1; i < (int) univ_level.size(); ++i) {
            printf("universal level [%d]: ", i);
            for (auto &u : univ_level[i]) {
                printf(" %d", u);
            }
            printf("\n");
        }

        for (i = 1; i < (int) exist_level.size(); ++i) {
            printf("existential level [%d]: ", i);
            for (auto &u : exist_level[i]) {
                printf(" %d", u);
            }
            printf("\n");
        }

        for (i = 1; i < (int) node_level.size(); ++i) {
            printf("dependency set id at level [%d]: ", i);
            for (auto &u : node_level[i]) {
                printf(" %d", u);
            }
            printf("\n");
        }
    }
};

struct formula {
    // clause is a set of literals
    vector<vector<int>> clauses;
    // dep is a vector of set of universal variables a variable depends on
    vector<set<int>> dep;
    // univ is a set of universal variables
    set<int> univ;
    closure T;
    void init(int nv, int nc) {
        dep = vector<set<int>>(nv + 1, set<int>());
        univ = set<int>();
        clauses = vector<vector<int>>();
    }

    void universal_reduction(int index) {
        vector<int> literal;
        multiset<int> uv;
        for (auto &l : clauses[index]) {
            for (auto &v : dep[abs(l)]) {
                uv.insert(v);
            }
        }

        for (auto &l : clauses[index]) {
            if (univ.find(abs(l)) == univ.end()) {
                literal.push_back(l);
            } else {
                uv.erase(uv.find(abs(l)));
                if (uv.find(abs(l)) != uv.end()) {
                    uv.insert(abs(l));
                    literal.push_back(l);
                }
            }
        }

        clauses[index] = literal;
    }

    // assume the DQBF is in DQBF^tree
    void compute_closure() {
        int i;
        for (i = 1; i < (int) dep.size(); ++i) {
            if (univ.find(i) == univ.end()) T.depset[dep[i]].push_back(i);
        }

        T.find_closure();
        T.construct_closure_tree();
        T.show();
    }

    void dqbf2qbf(string outpath) {
        int i;
        int nv = dep.size() - 1;
        FILE *fp = fopen(outpath.c_str(), "w");
        for (i = 1; i < (int) T.node_level.size(); ++i) {
            vector<vector<int>> nextclauses;
            for (auto &clause : clauses) {
                map<int, vector<int>> c;
                for (auto &l : clause) {
                    if (abs(l) < (int) dep.size()) {
                        int tid = T.var2id[abs(l)];
                        if (T.level[tid] >= i) {
                            // literals of the original formula
                            for (auto &deps_id : T.node_level[i]) { 
                                if (T.id[tid] >= T.id[deps_id] && T.id[tid] <= T.id[deps_id] + T.sz[deps_id] - 1) {
                                    c[deps_id].push_back(l);
                                }
                            }    
                        }
                        
                    }
                }

                if ((int) c.size() < 2) {
                    nextclauses.push_back(clause);
                } else {
                    int mx = c.rbegin()->first;
                    for (auto &l : clause) {
                        if (abs(l) < (int) dep.size() && T.level[T.var2id[abs(l)]] < i) {
                            c[mx].push_back(l);
                        }

                        if (abs(l) > dep.size()) {
                            c[mx].push_back(l);
                        }
                    }

                    for (auto &iter : c) {
                        if (iter.first < mx) {
                            iter.second.push_back(++nv);
                            c[mx].push_back(-nv);
                            T.exist_level[i-1].push_back(nv);
                        }
                    }

                    for (auto &iter : c) {
                        vector<int> lits;
                        for (auto &l : iter.second) {
                            lits.push_back(l);
                        }

                        nextclauses.push_back(lits);
                    }
                }
            }


            clauses = nextclauses;
        
            printf("after step [%d]: %d variables and %d clauses\n", i, nv, (int) clauses.size());

            for (auto &clause : clauses) {
                for (auto &l : clause) {
                    printf("%d ", l);
                }
                printf("\n");
            }
        }    

        fprintf(fp, "p cnf %d %d\n", nv, (int) clauses.size());

        for (i = 1; i < (int) T.node_level.size(); ++i) {
            if (!T.univ_level[i].empty()) {
                fprintf(fp, "a");
                for (auto &u : T.univ_level[i]) {
                    fprintf(fp, " %d", u);
                }   
                fprintf(fp, " 0\n");
            }

            if (!T.exist_level[i].empty()) {
                fprintf(fp, "e");
                for (auto &u : T.exist_level[i]) {
                    fprintf(fp, " %d", u);
                }   
                fprintf(fp, " 0\n");
            }
        }

        for (auto &clause : clauses) {
            for (auto &l : clause) {
                fprintf(fp, "%d ", l);
            }
            fprintf(fp, "0\n");
        }

        fclose(fp);
    }

    // print out the dqdimacs file
    void show() {
        int i;
        printf("p cnf %d %d\n", (int) dep.size(), (int)clauses.size());
        // print out the set of universal variables
        if (!univ.empty()) {
            printf("a");
            for (auto &u : univ) {
                printf(" %d", u);
            }
            printf(" 0\n");
        }

        // print out the dependencies
        for (i = 1; i < (int) dep.size(); ++i) {
            if (univ.find(i) == univ.end()) {
                printf("d %d", i);
                for (auto &u : dep[i]) {
                    printf(" %d", u);
                }
                printf(" 0\n");
            }
        }

        // print out all the clauses
        for (auto &c : clauses) {
            for (auto &l : c) {
                printf("%d ", l);
            }
            printf("0\n");
        }
    }
};

char line[MAX_SIZE];

// assume that the dqdimacs file is valid
formula read_dqdimacs(string path) {
    auto fp = fopen(path.c_str(), "r");
    formula f;
    char t1[6], t2[6];
    int nv, nc, i;
    // p cnf [numvar] [numclause]
    fscanf(fp, "%s%s%d%d\n", t1, t2, &nv, &nc);
    f.init(nv, nc);
    set<int> univ;
    while (fgets(line, MAX_SIZE, fp) != NULL) {
        vector<string> li;
        string curr;
        int N = strlen(line);
        if (N == 0) continue;
        for (i = 0 ; i < N; ++i) {
            if (line[i] == ' ' || line[i] == '\n') {
                if (!curr.empty()) {
                    li.push_back(curr);
                }
                curr = "";
            } else {
                curr.push_back(line[i]);
            }
        }

        if (!curr.empty()) {
            li.push_back(curr);
        }

        if (li.empty()) continue;
        // pop back the 0 at the end of the line
        li.pop_back();
        
        // trivial false
        if (li.empty()) {
            printf("UNSAT\n");
            exit(0);
        }

        if (li[0][0] == 'a') {
            for (i = 1; i < (int) li.size(); ++i) {
                univ.insert(stoi(li[i]));
                f.univ.insert(stoi(li[i]));
                f.dep[stoi(li[i])].insert(stoi(li[i]));
            }
        } else if (li[0][0] == 'e') {
            for (i = 1; i < (int) li.size(); ++i) {
                for (auto &u : univ) {
                    f.dep[stoi(li[i])].insert(u);
                }                
            }
        } else if (li[0][0] == 'd') {
            for (i = 2; i < (int) li.size(); ++i) {
                f.dep[stoi(li[1])].insert(stoi(li[i]));               
            }
        } else {
            // it is a clause
            f.clauses.push_back(vector<int>());
            for (i = 0; i < (int) li.size(); ++i) {
                f.clauses[(int) f.clauses.size() - 1].push_back(stoi(li[i]));
            }
            f.universal_reduction((int) f.clauses.size() - 1);
        }
    }

    fclose(fp);

    return f;
}

int main(int argc, char *argv[]) {
    if (argc != 3) {
        printf("Usage ./convert [input_file_path] [out_file_path]\n");
        return 0;
    }

    formula f = read_dqdimacs(string(argv[1]));
    f.show();
    f.compute_closure();
    f.dqbf2qbf(string(argv[2]));
    return 0;
}