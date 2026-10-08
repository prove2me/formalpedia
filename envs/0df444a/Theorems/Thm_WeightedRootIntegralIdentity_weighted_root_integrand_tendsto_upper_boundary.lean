-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_integrand_tendsto_upper_boundary
-- name    : WeightedRootIntegralIdentity.weighted_root_integrand_tendsto_upper_boundary
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T07:52:46.898569+00:00
-- url     : https://prove2.me/theorems/f8cf1c17-fa9c-44c7-a224-da219c452944
-- title:
--   Pointwise upper boundary limit of the weighted-root integrand
-- statement:
--   Let $a_0,\dots,a_{n-1}$ and $w_0,\dots,w_{n-1}$ be real. At a real point $x\ne0$ distinct from each $a_i$, the principal-power integrand has the upper boundary limit
--   $$\lim_{\varepsilon\to0^+}\frac{\prod_{i=0}^{n-1}(x+i\varepsilon-a_i)^{w_i}}{x+i\varepsilon}
--   =\frac{\prod_{i=0}^{n-1}(x-a_i)^{w_i}}{x}.$$
--
--   The finitely many excluded branch points are negligible for interval integration. This pointwise statement is an input to the subsequent dominated-convergence step.
-- source:
--   Principal upper-boundary passage in the keyhole-contour argument of K B Dave, Mathematics Stack Exchange, https://math.stackexchange.com/a/4245016.

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_tendsto_real_of_upper_half_plane
open Filter Set Topology
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_integrand_tendsto_upper_boundary
    (n : ℕ) (a w : ℕ → ℝ) (x : ℝ)
    (hx : x ≠ 0) (hxa : ∀ i < n, x ≠ a i) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (∏ i ∈ Finset.range n,
          (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
          ((x : ℂ) + ε * Complex.I))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)) / (x : ℂ))) := by sorry

end WeightedRootIntegralIdentity
