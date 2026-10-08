-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_im_integrand_ae_tendsto_upper_boundary
-- name    : WeightedRootIntegralIdentity.weighted_root_im_integrand_ae_tendsto_upper_boundary
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T08:05:52.247718+00:00
-- url     : https://prove2.me/theorems/bf93a85c-04ec-4dba-9c9a-d938b4f6eaee
-- title:
--   Almost-everywhere upper boundary convergence of the imaginary integrand
-- statement:
--   On a finite interval, assume the exceptional points $x=0$ and $x=a_i$ are null for the restricted Lebesgue measure. Then, almost everywhere on the interval,
--   $$\operatorname{Im}\!\left(\frac{\prod_i(x+i\varepsilon-a_i)^{w_i}}{x+i\varepsilon}\right)
--   \to\operatorname{Im}\!\left(\frac{\prod_i(x-a_i)^{w_i}}{x}\right)$$
--   as $\varepsilon\to0^+$. This is the exact almost-everywhere convergence input for a dominated-convergence argument.
-- source:
--   Almost-everywhere wrapper around the pointwise boundary limit in K B Dave, Mathematics Stack Exchange, https://math.stackexchange.com/a/4245016.

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_im_integrand_tendsto_upper_boundary
open Filter Set MeasureTheory Topology
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_im_integrand_ae_tendsto_upper_boundary
    (n : ℕ) (a w : ℕ → ℝ) (l r : ℝ)
    (hx : ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)), x ≠ 0)
    (hxa : ∀ i < n, ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)), x ≠ a i) :
    ∀ᵐ x : ℝ ∂(volume.restrict (uIcc l r : Set ℝ)),
      Filter.Tendsto
        (fun ε : ℝ =>
          ((∏ i ∈ Finset.range n,
            (((x : ℂ) + ε * Complex.I) - (a i : ℂ)) ^ (w i : ℂ)) /
            ((x : ℂ) + ε * Complex.I)).im)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (((∏ i ∈ Finset.range n,
            ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)) / (x : ℂ)).im)) := by sorry

end WeightedRootIntegralIdentity
