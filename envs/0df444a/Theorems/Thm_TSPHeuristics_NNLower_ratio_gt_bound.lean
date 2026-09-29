-- Prove2me | Theorems.Thm_TSPHeuristics_NNLower_ratio_gt_bound
-- name    : TSPHeuristics.NNLower.ratio_gt_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:28:41.551967+00:00
-- url     : https://prove2.me/theorems/17dc1011-f0b7-4e03-bd4f-924f35b58be2
-- title:
--   $(L_i+l_i-1)/n>\frac13\lg(n+1)+\frac49$ for $i\ge3$
-- statement:
--   Let $i\ge3$ and $n=2^{i+1}-1$. Then
--   $$\frac{L_i+l_i-1}{n}>\frac13\lg(n+1)+\frac49,$$
--   where $\lg$ is the logarithm to base 2 (so $\lg(n+1)=i+1$). This is the sentence "This ratio is greater than the ratio indicated in the theorem" of p. 569, for $m=i+1>3$. The inequality fails for $i=1,2$, which is why Theorem 2 requires $m>3$.
--
--   **Formalization Note** The ratio is multiplied out by $n>0$: the Lean statement is $(\frac13\lg(n+1)+\frac49)\cdot n<L_i+l_i-1$.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 569 ("This ratio is greater than the ratio indicated in the theorem.")

import Mathlib
import Definitions.Def_TSPHeuristics_NNLower_LowerBoundFamily

namespace TSPHeuristics.NNLower

/-- p. 569: for `i ≥ 3` (i.e. `m = i + 1 > 3`), the ratio `(L_i + l_i − 1)/n` of `Ḡ_i`, with
`n = 2^(i+1) − 1`, exceeds the bound `(1/3) lg(n + 1) + 4/9` of Theorem 2 (ratio multiplied
out by `n > 0`). -/
theorem ratio_gt_bound (i : ℕ) (hi : 3 ≤ i) :
    (1 / 3 * Real.logb 2 ((numNodes i : ℝ) + 1) + 4 / 9) * (numNodes i : ℝ) <
      pathLength i + ell i - 1 := by sorry

end TSPHeuristics.NNLower
