-- Prove2me | Theorems.Thm_P7ThreeColor_Lemma11_claim_13
-- name    : P7ThreeColor.Lemma11.claim_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:50.322567+00:00
-- url     : https://prove2.me/theorems/089decc1-8358-4ba3-a71e-b722b405a412
-- title:
--   Claim 13, p. 16 — for x, y ∈ Xᵢ there is an edge between {x, nⱼ, nₖ} and {y, nⱼ(y), nₖ(y)}
-- statement:
--   Let $G$ be a finite connected $P_7$-free graph with a palette $L$ (lists $L(v) \subseteq \{1,2,3\}$), and let $S$ be a seed of $(G,L)$ such that $(G,L,S)$ satisfies the hypotheses of Lemma 11: adjacent vertices $v \in S$, $w \in N(S)$ have disjoint lists, and the set $X$ of vertices with $|L(v)| = 3$ is stable, anticomplete to $V(G) \setminus (\overline{S} \cup X)$, and contains no vertex with a connected neighborhood. For $i \in \{1,2,3\}$ let $D_i = \{v \in N(S) : L(v) = \{1,2,3\}\setminus\{i\}\}$ and $N_i(x) = N(x) \cap D_i$.
--
--   Let $\{i,j,k\} = \{1,2,3\}$ and let $x, y \in X$. Let $n_j \in N_j(x)$ and $n_k \in N_k(x)$ be non-adjacent, and let $m_j \in N_j(y)$ and $m_k \in N_k(y)$ be non-adjacent (so $x, y \in X_i$, the set of vertices of $X$ for which $N_j$ is not complete to $N_k$, and $m_j, m_k$ is an admissible choice of the paper's $n_j(y), n_k(y)$). Then
--
--   $$\text{some vertex of } \{x, n_j, n_k\} \text{ is adjacent to some vertex of } \{y, m_j, m_k\}.$$
--
--   This is the structural core of the proof of Lemma 11: it is what lets the algorithm handle all the vertices of $X_i$ at once when it refines the palette, and ultimately reduces list 3-coloring of $P_7$-free graphs to 2-SAT.
--
--   **Formalization Note** The paper fixes one pair $n_j(y), n_k(y)$ for each $y \in X_i$ by an arbitrary choice; the statement here holds for every non-adjacent pair $m_j \in N_j(y)$, $m_k \in N_k(y)$, which is the claim for every possible choice. The case $x = y$ is allowed. Colors $1,2,3$ are `0,1,2` in `Fin 3`.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 16, Claim 13

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Setting

namespace P7ThreeColor.Lemma11

/-- Claim 13, p. 16. Let `{i, j, k} = {1, 2, 3}` and `x, y ∈ X_i`; let `n_j ∈ N_j(x)` and
`n_k ∈ N_k(x)` be non-adjacent, and let `m_j ∈ N_j(y)`, `m_k ∈ N_k(y)` be non-adjacent (any
admissible choice of the paper's `n_j(y), n_k(y)`). Then some vertex of `{x, n_j, n_k}` is
adjacent to some vertex of `{y, m_j, m_k}`. -/
theorem claim_13 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → Finset (Fin 3)) (S : Finset V) (hyp : Lemma11Hyp G L S)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x y : V) (hx : x ∈ X L) (hy : y ∈ X L)
    (nj nk : V) (hnj : nj ∈ Ni G L S j x) (hnk : nk ∈ Ni G L S k x) (hn : ¬ G.Adj nj nk)
    (mj mk : V) (hmj : mj ∈ Ni G L S j y) (hmk : mk ∈ Ni G L S k y) (hm : ¬ G.Adj mj mk) :
    ∃ a ∈ ({x, nj, nk} : Finset V), ∃ b ∈ ({y, mj, mk} : Finset V), G.Adj a b := by sorry

end P7ThreeColor.Lemma11
