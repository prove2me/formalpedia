-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_im_integrand_tendsto_upper_boundary
-- name    : WeightedRootIntegralIdentity.weighted_root_im_integrand_tendsto_upper_boundary
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T07:59:25.067741+00:00
-- url     : https://prove2.me/theorems/cb079a41-e839-466d-951a-2566273f96f2
-- title:
--   Pointwise imaginary-part limit of the upper boundary integrand
-- statement:
--   Under the hypotheses of the weighted-root boundary limit, taking imaginary parts preserves convergence:
--   $$\operatorname{Im}\!\left(\frac{\prod_i(x+i\varepsilon-a_i)^{w_i}}{x+i\varepsilon}\right)
--   \longrightarrow
--   \operatorname{Im}\!\left(\frac{\prod_i(x-a_i)^{w_i}}{x}\right)$$
--   as $\varepsilon\to0^+$. This is the real-valued pointwise convergence statement used in the subsequent interval-integral limit.
-- source:
--   Continuous-image step following the weighted-root boundary limit in K B Dave, Mathematics Stack Exchange, https://math.stackexchange.com/a/4245016.

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_integrand_tendsto_upper_boundary
open Filter Set Topology
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_im_integrand_tendsto_upper_boundary
    (n : ℕ) (a w : ℕ → ℝ) (x : ℝ)
    (hx : x ≠ 0) (hxa : ∀ i < n, x ≠ a i) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ((∏ i ∈ Finset.range n,
          (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) + ε * Complex.I)).im)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)) / (x : ℂ)).im)) := by sorry

end WeightedRootIntegralIdentity
