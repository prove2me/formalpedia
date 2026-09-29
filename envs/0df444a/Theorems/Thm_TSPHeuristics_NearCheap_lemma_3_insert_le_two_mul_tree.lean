-- Prove2me | Theorems.Thm_TSPHeuristics_NearCheap_lemma_3_insert_le_two_mul_tree
-- name    : TSPHeuristics.NearCheap.lemma_3_insert_le_two_mul_tree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:58:55.063018+00:00
-- url     : https://prove2.me/theorems/e828c9df-edf9-46d5-a5ec-dd77bd346b9f
-- title:
--   Lemma 3 — if every step satisfies (4.5), then INSERT ≤ 2·TREE
-- statement:
--   Let $(N, d)$ be a traveling salesman graph with $n \ge 1$ nodes and let $T_1, \dots, T_n$, $a_0, \dots, a_{n-1}$ be a run of an insertion method. Suppose that for every $1 \le i < n$,
--
--   $$
--   \mathrm{COST}(T_i, a_i) \le 2\, d(p,q) \quad \text{for all } p \in T_i,\ q \notin T_i. \qquad (4.5)
--   $$
--
--   Then for every spanning tree $M$ of $N$, the length INSERT of the final tour $T_n$ satisfies
--
--   $$
--   \mathrm{INSERT} \le 2\, w(M), \qquad (4.6)
--   $$
--
--   where $w(M)$ is the total length of the edges of $M$. In particular $\mathrm{INSERT} \le 2\cdot\mathrm{TREE}$, where TREE is the length of a minimal spanning tree.
--
--   The lemma reduces the analysis of an insertion rule to the single local inequality (4.5).
--
--   **Formalization Note** The paper states (4.6) for TREE, the length of a minimal spanning tree; the Lean statement asserts it for every spanning tree, which is equivalent since TREE is the least tree length (and the paper's proof does not use minimality). The distance satisfies $d(i,i)=0$ (normalization).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 573, Lemma 3, eqs. (4.5), (4.6)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion
import Definitions.Def_TSPHeuristics_NearCheap_SpanningTree

open Classical

namespace TSPHeuristics.NearCheap

theorem lemma_3_insert_le_two_mul_tree {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a)
    (h45 : ∀ i, 1 ≤ i → i < n → ∀ p ∈ T i, ∀ q, q ∉ T i →
      TSPHeuristics.Shared.insCost d (T i) (a i) ≤ 2 * d p q)
    (M : SimpleGraph (Fin n)) (hM : M.IsTree) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ 2 * treeWeight d M := by sorry

end TSPHeuristics.NearCheap
