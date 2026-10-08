-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_upper_rectangle_integral_eq_zero
-- name    : WeightedRootIntegralIdentity.weighted_root_upper_rectangle_integral_eq_zero
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T15:00:54.437143+00:00
-- url     : https://prove2.me/theorems/16f255ca-aa0a-4990-b30f-b8eba0c89554
-- title:
--   Cauchy–Goursat identity on an upper truncated rectangle
-- statement:
--   Let $a_0,\ldots,a_{n-1}$ and $w_0,\ldots,w_{n-1}$ be real, and put
--   $$f(z)=\frac{\prod_{i=0}^{n-1}(z-a_i)^{w_i}}{z},$$
--   with principal complex powers. For a rectangle $[l,r]\times[\varepsilon,H]$ contained in the upper half-plane, where $0<\varepsilon\le H$, the oriented sum of the integrals of $f$ along its four edges is zero.
--
--   This is the finite Cauchy–Goursat identity used before sending the horizontal and vertical truncation parameters to their keyhole-contour limits.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, finite upper-half-plane contour step in the keyhole argument.

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_div_differentiableAt_of_im_ne_zero
open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_root_upper_rectangle_integral_eq_zero
    (n : ℕ) (a w : ℕ → ℝ) (l r ε H : ℝ)
    (hε : 0 < ε) (hεH : ε ≤ H) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x + ε * Complex.I)) -
        (∫ x : ℝ in l..r, f (x + H * Complex.I)) +
        Complex.I • (∫ y : ℝ in ε..H, f (r + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in ε..H, f (l + y * Complex.I)) = 0 := by sorry

end WeightedRootIntegralIdentity
