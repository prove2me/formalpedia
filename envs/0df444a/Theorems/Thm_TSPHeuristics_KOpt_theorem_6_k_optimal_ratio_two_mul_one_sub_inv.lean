-- Prove2me | Theorems.Thm_TSPHeuristics_KOpt_theorem_6_k_optimal_ratio_two_mul_one_sub_inv
-- name    : TSPHeuristics.KOpt.theorem_6_k_optimal_ratio_two_mul_one_sub_inv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:01:44.437278+00:00
-- url     : https://prove2.me/theorems/8f16e289-31dd-48c8-afca-15dab1367638
-- title:
--   Theorem 6 — a tour $k$-optimal for all $k\le n/4$ with LOCALOPT/OPTIMAL $= 2(1-1/n)$
-- statement:
--   For each $n\ge 8$ there is a traveling salesman graph on $n$ nodes with $\mathrm{OPTIMAL}>0$ having a tour that is $k$-optimal for every $k\le n/4$ and whose length LOCALOPT satisfies
--   $$\frac{\mathrm{LOCALOPT}}{\mathrm{OPTIMAL}}=2\left(1-\frac1n\right).\qquad(7.1)$$
--
--   Local optimality under $k$-changes with $k$ up to a quarter of the number of cities therefore does not guarantee a ratio better than $2(1-1/n)$.
--
--   **Formalization Note** The ratio is multiplied out: `tourLength d τ = 2 * (1 - 1/n) * optimal d`. `0 < optimal d` is the paper's standing assumption (1.1) (p. 564), which excludes the identically zero distance that would make the statement trivial. $k\le n/4$ is written $4k\le n$ for natural $k$; one tour serves every such $k$, as printed. The bound $n\ge 8$ is the printed one.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, p. 579, Theorem 6, (7.1); proof pp. 579–581

import Mathlib
import Definitions.Def_TSPHeuristics_KOpt_KOptimal

namespace TSPHeuristics.KOpt

theorem theorem_6_k_optimal_ratio_two_mul_one_sub_inv (n : ℕ) (hn : 8 ≤ n) :
    ∃ d : Fin n → Fin n → ℝ, TSPHeuristics.Shared.IsTSPDist d ∧ 0 < TSPHeuristics.Shared.optimal d ∧
      ∃ τ : Equiv.Perm (Fin n), (∀ k : ℕ, 4 * k ≤ n → IsKOptimalTour d k τ) ∧
        TSPHeuristics.Shared.tourLength d τ = 2 * (1 - 1 / (n : ℝ)) * TSPHeuristics.Shared.optimal d := by sorry

end TSPHeuristics.KOpt
