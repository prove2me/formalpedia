-- Prove2me | Theorems.Thm_QGraphColl_lemma_C_2
-- name    : QGraphColl.lemma_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:27.45142+00:00
-- url     : https://prove2.me/theorems/9aadbbd0-124b-4e44-84ed-f9f6014f8596
-- title:
--   Lemma C.2 — exact partition into $O((\log n)^3)$ pieces with degrees in $[d_i/\gamma,d_i]$, $\gamma=32(\log n)^2$
-- statement:
--   Let $n=|V|\ge2$ and $\gamma=32(\log_2 n)^2$. There is an absolute constant $C_j$ such that every bipartite graph $G$ on $V$ with sides $A,B$ admits pieces $F_1,\dots,F_j$ with bounds $d_1(i),d_2(i)$, determined by $G$ alone (no input queries), such that
--
--   1. $j\le C_j(\log_2 n)^3$;
--   2. every piece is nonempty and contained in $G$, the pieces are pairwise edge-disjoint, and their union is $G$;
--   3. every vertex of $A$ incident to $F_i$ has degree in $F_i$ between $d_1(i)/\gamma$ and $d_1(i)$, and every vertex of $B$ incident to $F_i$ between $d_2(i)/\gamma$ and $d_2(i)$;
--   4. marked volume is additive: $\mathrm{vol}(G,S,x)=\sum_i\mathrm{vol}(F_i,S,x)$ for every $S$ and $x$.
--
--   This is the partition (Algorithm 13, partition_edges) into pieces with comparable degrees on each side, on which the volume reduction of Lemma 4.7 runs.
--
--   Differences from the source:
--   - encoding: j = O((log n)³), γ = 32(log n)², n the size of the known graph → j ≤ C_j·(log₂ |V|)³ with C_j absolute, γ = 32(log₂ |V|)², |V| ≥ 2; reason: logarithms are base two (p.12); n ≥ 2 keeps log n > 0
--   - reading: Algorithm 13 (partition_edges) partitions a known bipartite graph, without input queries, and returns triples (F, d1, d2) → there exist j, pieces F : Fin j → SimpleGraph V and bounds d₁, d₂ : Fin j → ℝ, depending on G alone (no input appears in the construction); reason: the construction uses only the known graph and its query cost is zero (pp.24, 49); the existence of the partition with these guarantees is what Lemmas C.1 and 4.8 use (paper.md decision 4)
--   - encoding: a bipartite graph with sides A, B → IsSides G A B on a vertex type V that may contain further labels outside A ∪ B; reason: such labels are isolated (every edge joins A to B), and the conclusions concern only edges and the labels incident to them; every bipartite graph has such sides
--   - encoding: partitions G into nonempty pieces; F is an exact edge list on its incident labels; every vertex on side i → F i ≠ ⊥, F i ≤ G, pairwise Disjoint, ⨆ F i = G; the degree window for every v ∈ A (resp. B) with deg_{F i}(v) > 0; reason: the pieces live on the same labels; 'on its incident labels' restricts to vertices of positive degree in the piece
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Lemma C.2, p.49 (Algorithm 13 partition_edges)

import Mathlib
import Definitions.Def_QGraphColl_gc
import Definitions.Def_QGraphColl_vol
import Definitions.Def_QGraphColl_restrict

namespace QGraphColl

/-- **Lemma C.2** (Exact partition; A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), p.49). Algorithm 13 partitions a known bipartite graph
into `j = O((log n)³)` nonempty pieces, without input queries. It returns triples `(F, d_1, d_2)`,
where `F` is an exact edge list on its incident labels and every vertex on side `i` has degree in
`[d_i/γ, d_i]`, for `γ = 32(log n)²`. Marked volume is additive over the pieces.

**Formalization Note.**
* Algorithm 13 (`partition_edges`) is stated as the existence of the partition it returns: `j`
  pieces `F i` on the same labels with bounds `d₁ i`, `d₂ i`. "Without input queries": the
  pieces depend on `G`, `A`, `B` only (no input `x` occurs before them).
* `n = |V| ≥ 2`, logarithms base two; the constant `C_j` of `O((log n)³)` is absolute.
* "Partitions": the pieces are nonempty, contained in `G`, pairwise edge-disjoint, and their
  supremum is `G`. "Every vertex on side `i`" ranges over the incident labels of the piece (positive
  degree in `F i`); side 1 is `A`, side 2 is `B`.
* Additivity is stated for every `S` and every input `x`. -/
theorem lemma_C_2 :
    ∃ Cj : ℝ, 0 < Cj ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], 2 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (A B : Finset V), IsSides G A B →
        ∃ (j : ℕ) (F : Fin j → SimpleGraph V) (d₁ d₂ : Fin j → ℝ),
          (j : ℝ) ≤ Cj * Real.logb 2 (Fintype.card V : ℝ) ^ 3 ∧
          (∀ i, F i ≠ ⊥ ∧ F i ≤ G) ∧
          Pairwise (fun i i' => Disjoint (F i) (F i')) ∧
          (⨆ i, F i) = G ∧
          (∀ i, ∀ v ∈ A, 0 < deg (F i) v →
            d₁ i / (32 * Real.logb 2 (Fintype.card V : ℝ) ^ 2) ≤ (deg (F i) v : ℝ) ∧
              (deg (F i) v : ℝ) ≤ d₁ i) ∧
          (∀ i, ∀ v ∈ B, 0 < deg (F i) v →
            d₂ i / (32 * Real.logb 2 (Fintype.card V : ℝ) ^ 2) ≤ (deg (F i) v : ℝ) ∧
              (deg (F i) v : ℝ) ≤ d₂ i) ∧
          (∀ (S : Finset V) (x : V → Bool), vol G S x = ∑ i, vol (F i) S x) := by sorry

end QGraphColl
