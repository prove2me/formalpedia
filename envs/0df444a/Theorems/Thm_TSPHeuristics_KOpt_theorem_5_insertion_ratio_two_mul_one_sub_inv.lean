-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_theorem_5_insertion_ratio_two_mul_one_sub_inv
-- name    : TSPHeuristics.KOpt.theorem_5_insertion_ratio_two_mul_one_sub_inv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:57:33.377581+00:00
-- url     : https://prove2.me/theorems/21f34d80-c646-4034-8d32-47f2f368343b
-- title:
--   Theorem 5 — nearest and cheapest insertion can reach INSERT/OPTIMAL $= 2(1-1/n)$
-- statement:
--   For every $n\ge 6$ there is a traveling salesman graph $(N,d)$ on $n$ nodes with $\mathrm{OPTIMAL}>0$ on which both nearest insertion and cheapest insertion can produce a tour of length INSERT with
--   $$\frac{\mathrm{INSERT}}{\mathrm{OPTIMAL}}=2\left(1-\frac1n\right).\qquad(4.14)$$
--
--   Together with the Corollary to Theorem 4 (INSERT $\le 2(1-1/n)\cdot$OPTIMAL for both methods) this shows that the bound $2(1-1/n)$ is attained for every $n\ge 6$.
--
--   **Formalization Note** The ratio is multiplied out: `cycleLength d (T n) = 2 * (1 - 1/n) * optimal d`. The conjunct `0 < optimal d` is the paper's standing assumption (1.1) (p. 564, which excludes the identically zero distance); without it the zero distance would make the statement trivial. "For either the nearest insertion or cheapest insertion methods" is read as both methods on one and the same graph, which is what the proof gives; each method comes with its own run ($T_1,\dots,T_n$ and $a_0,\dots,a_{n-1}$), existentially quantified since ties may be resolved suitably.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 575, Theorem 5, (4.14)

import Mathlib
import Definitions.Def_TSPHeuristics_Shared_Insertion

namespace TSPHeuristics.KOpt

theorem theorem_5_insertion_ratio_two_mul_one_sub_inv (n : ℕ) (hn : 6 ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsNearestRule d T a ∧
        TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) ∧
      (∃ (T : ℕ → List (Fin n)) (a : ℕ → Fin n), TSPHeuristics.Shared.IsInsertionRun d T a ∧ TSPHeuristics.Shared.IsCheapestRule d T a ∧
        TSPHeuristics.Shared.cycleLength d (T n) = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d) := by sorry

end TSPHeuristics.KOpt
