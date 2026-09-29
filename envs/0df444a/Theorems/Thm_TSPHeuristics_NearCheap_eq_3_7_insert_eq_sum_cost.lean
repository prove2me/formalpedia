-- Prove2me | Theorems.Thm_TSPHeuristics_NearCheap_eq_3_7_insert_eq_sum_cost
-- name    : TSPHeuristics.NearCheap.eq_3_7_insert_eq_sum_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:57:22.168328+00:00
-- url     : https://prove2.me/theorems/d22a2680-8f3c-485c-88cf-fe3c01b4c576
-- title:
--   Eq. (3.7) — INSERT is the sum of the insertion costs
-- statement:
--   Let $(N, d)$ be a traveling salesman graph with $n \ge 1$ nodes, and let $T_1, \dots, T_n$, $a_0, \dots, a_{n-1}$ be a run of an insertion method: $T_1 = \{a_0\}$ and $T_{i+1} = \mathrm{TOUR}(T_i, a_i)$ with $a_i \notin T_i$ for $1 \le i < n$. Then the length INSERT of the final tour $T_n$ is
--
--   $$
--   \mathrm{INSERT} = \sum_{i=1}^{n-1} \mathrm{COST}(T_i, a_i). \qquad (3.7)
--   $$
--
--   This telescoping identity turns bounds on individual insertion steps into a bound on the tour the insertion method returns; it holds for every insertion method, whatever rule selects the nodes $a_i$.
--
--   **Formalization Note** It uses that the one-node subtour $T_1$ has length $0$, which the normalization $d(i,i) = 0$ provides (the paper treats a one-node subtour as a tour without edges).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 571, eq. (3.7) (proof of Theorem 3); used on p. 574 in the proof of Lemma 3

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem eq_3_7_insert_eq_sum_cost {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) = ∑ i ∈ Finset.Ico 1 n, TSPHeuristics.Shared.insCost d (T i) (a i) := by sorry

end TSPHeuristics.NearCheap
