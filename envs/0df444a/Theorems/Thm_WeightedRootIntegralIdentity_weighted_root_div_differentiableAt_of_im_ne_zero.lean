-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_div_differentiableAt_of_im_ne_zero
-- name    : WeightedRootIntegralIdentity.weighted_root_div_differentiableAt_of_im_ne_zero
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T14:51:36.098776+00:00
-- url     : https://prove2.me/theorems/d19bb928-6332-496b-8bfd-3d483825dd54
-- title:
--   Holomorphicity of the weighted-root quotient in both open half-planes
-- statement:
--   For the principal-power weighted root product F(z) = ∏ᵢ(z-aᵢ)^{wᵢ}, the quotient F(z)/z is complex differentiable at every point with nonzero imaginary part.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, analytic-domain prerequisite for the keyhole contour differential F(z) dz / z.

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_differentiableAt_of_shift_mem_slitPlane
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_div_differentiableAt_of_im_ne_zero
    (n : ℕ) (a w : ℕ → ℝ) (z : ℂ)
    (hz : z.im ≠ 0) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z) z := by sorry

end WeightedRootIntegralIdentity
