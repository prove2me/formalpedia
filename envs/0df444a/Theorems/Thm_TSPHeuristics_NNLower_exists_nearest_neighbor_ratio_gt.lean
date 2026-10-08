-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_exists_nearest_neighbor_ratio_gt
-- name    : TSPHeuristics.NNLower.exists_nearest_neighbor_ratio_gt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:29:17.800601+00:00
-- url     : https://prove2.me/theorems/d2a0381c-80bd-474a-99ad-fb1a56819f45
-- title:
--   Theorem 2: nearest neighbor can be $\frac13\lg(n+1)+\frac49$ times optimal
-- statement:
--   For each integer $m>3$ there exists a traveling salesman graph with $n=2^m-1$ nodes (a complete graph whose distance $d$ is symmetric, nonnegative and satisfies the triangle inequality) and a tour of it produced by the nearest neighbor algorithm (some start node, some resolution of ties), of length NEARNEIBER, such that OPTIMAL $>0$ and
--   $$\frac{\mathrm{NEARNEIBER}}{\mathrm{OPTIMAL}}>\frac13\lg(n+1)+\frac49 .$$
--   Here $\lg$ is the logarithm to base 2 and OPTIMAL is the length of an optimal tour.
--
--   Together with Theorem 1 (NEARNEIBER/OPTIMAL $\le\frac12\lceil\lg n\rceil+\frac12$ for every nearest-neighbor tour), this shows that the worst-case ratio of the nearest neighbor heuristic grows logarithmically in $n$.
--
--   **Formalization Note** The ratio is multiplied out: the Lean conclusion is $(\frac13\log_2(n+1)+\frac49)\cdot\mathrm{OPTIMAL}<\mathrm{NEARNEIBER}$, with $\mathrm{OPTIMAL}>0$ (the paper's (1.1)) stated explicitly. Nodes are `Fin (2^m - 1)`; the distance also satisfies the normalization $d(a,a)=0$. The claim is existential in both the instance and the run, as in the paper ("with suitable resolution of ties", p. 568).
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 566, Theorem 2

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_TSPModel

namespace TSPHeuristics.NNLower

/-- Theorem 2 (Rosenkrantz–Stearns–Lewis 1977, p. 566): for each `m > 3` there is a traveling
salesman graph with `n = 2^m − 1` nodes and a run of the nearest neighbor algorithm on it whose
tour length NEARNEIBER satisfies `NEARNEIBER / OPTIMAL > (1/3) lg(n + 1) + 4/9`
(ratio multiplied out; `OPTIMAL > 0` is the paper's (1.1)). -/
theorem exists_nearest_neighbor_ratio_gt (m : ℕ) (hm : 3 < m) :
    ∃ d : Fin (2 ^ m - 1) → Fin (2 ^ m - 1) → ℝ, IsTSPDist d ∧ 0 < optimal d ∧
      ∃ τ : Equiv.Perm (Fin (2 ^ m - 1)), IsNearestNeighborTour d τ ∧
        (1 / 3 * Real.logb 2 (((2 ^ m - 1 : ℕ) : ℝ) + 1) + 4 / 9) * optimal d < tourLength d τ := by sorry

end TSPHeuristics.NNLower
