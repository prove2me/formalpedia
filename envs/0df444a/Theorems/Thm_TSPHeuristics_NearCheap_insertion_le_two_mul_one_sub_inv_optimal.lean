-- Prove2me | Theorems.Thm_TSPHeuristics_NearCheap_insertion_le_two_mul_one_sub_inv_optimal
-- name    : TSPHeuristics.NearCheap.insertion_le_two_mul_one_sub_inv_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:01:33.949899+00:00
-- url     : https://prove2.me/theorems/ebc35a9f-c79d-4c6b-89e8-10fc62caf8a4
-- title:
--   Corollary to Theorem 4 — nearest and cheapest insertion: INSERT ≤ 2(1 − 1/n)·OPTIMAL
-- statement:
--   Let $(N, d)$ be a traveling salesman graph on $n \ge 1$ nodes (symmetric, nonnegative distances satisfying the triangle inequality), and let INSERT be the length of a tour obtained by **nearest insertion** or by **cheapest insertion**, from any start node and with any resolution of ties. Then
--
--   $$
--   \mathrm{INSERT} \le 2\Bigl(1 - \frac1n\Bigr)\cdot \mathrm{OPTIMAL}, \qquad (4.12)
--   $$
--
--   where OPTIMAL is the length of an optimal tour.
--
--   This sharpens Theorem 4 ($\mathrm{INSERT}/\mathrm{OPTIMAL} < 2$) to the exact constant $2(1 - 1/n)$; the paper shows elsewhere (Theorem 5) that this constant is attained, so the bound is the worst case of both heuristics.
--
--   **Formalization Note** The ratio (4.12) is multiplied out, so no nontriviality hypothesis on $d$ is needed (if $d \equiv 0$ both sides are $0$). The run is any insertion-method run $T_1 = \{a_0\}, T_{i+1} = \mathrm{TOUR}(T_i, a_i)$ satisfying the nearest-insertion rule (4.2) or the cheapest-insertion rule (4.3), with an arbitrary start node and arbitrary ties. The distance satisfies $d(i,i)=0$ (normalization); nodes are `Fin n`.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 574, Corollary to Theorem 4, eq. (4.12)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.NearCheap

theorem insertion_le_two_mul_one_sub_inv_optimal {n : ℕ} (hn : 1 ≤ n) (d : Fin n → Fin n → ℝ)
    (hd : TSPHeuristics.Shared.IsTSPDist d) (T : ℕ → List (Fin n)) (a : ℕ → Fin n) (hrun : TSPHeuristics.Shared.IsInsertionRun d T a)
    (hrule : TSPHeuristics.Shared.IsNearestRule d T a ∨ TSPHeuristics.Shared.IsCheapestRule d T a) :
    TSPHeuristics.Shared.cycleLength d (T n) ≤ 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.NearCheap
