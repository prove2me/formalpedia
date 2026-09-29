-- Prove2me | Theorems.Thm_TSPHeuristics_NearCheap_eq_4_11_tree_le_one_sub_inv_optimal
-- name    : TSPHeuristics.NearCheap.eq_4_11_tree_le_one_sub_inv_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:59:33.161467+00:00
-- url     : https://prove2.me/theorems/4c54966b-2c12-45ea-a9c8-bfc254ec45a3
-- title:
--   Eq. (4.11) — TREE ≤ (1 − 1/n)·OPTIMAL
-- statement:
--   Let $(N, d)$ be a traveling salesman graph with $n \ge 1$ nodes. Then there is a spanning tree $M$ of $N$ with
--
--   $$
--   w(M) \le \Bigl(1 - \frac1n\Bigr)\cdot \mathrm{OPTIMAL}, \qquad (4.11)
--   $$
--
--   that is, $\mathrm{TREE} \le (1 - 1/n)\cdot\mathrm{OPTIMAL}$, where TREE is the length of a minimal spanning tree and OPTIMAL the length of an optimal tour.
--
--   Combined with Lemma 3 this converts the bound $\mathrm{INSERT} \le 2\cdot\mathrm{TREE}$ into a bound relative to the optimal tour.
--
--   **Formalization Note** "TREE $\le c$" is stated as the existence of a spanning tree of length at most $c$, which is equivalent. At $n = 1$ the statement reads $0 \le 0$. The distance satisfies $d(i,i)=0$ (normalization).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 574, eq. (4.11)

import Mathlib
import Definitions.Def_TSPHeuristics_NearCheap_SpanningTree

open Classical

namespace TSPHeuristics.NearCheap

theorem eq_4_11_tree_le_one_sub_inv_optimal {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) :
    ∃ M : SimpleGraph (Fin n), M.IsTree ∧
      treeWeight d M ≤ (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.NearCheap
