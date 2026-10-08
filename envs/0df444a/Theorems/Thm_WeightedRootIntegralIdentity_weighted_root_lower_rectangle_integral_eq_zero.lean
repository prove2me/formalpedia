-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_lower_rectangle_integral_eq_zero
-- name    : WeightedRootIntegralIdentity.weighted_root_lower_rectangle_integral_eq_zero
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T15:08:32.213872+00:00
-- url     : https://prove2.me/theorems/a8ec0ea7-be53-4c10-a415-29565252224a
-- title:
--   Cauchy–Goursat identity on a lower truncated rectangle
-- statement:
--   Let $a_0,\ldots,a_{n-1}$ and $w_0,\ldots,w_{n-1}$ be real, and define
--   $$f(z)=\frac{\prod_{i=0}^{n-1}(z-a_i)^{w_i}}{z}$$
--   using principal complex powers. If $0<\varepsilon\le H$, then the oriented sum of the four edge integrals of $f$ around the rectangle $[l,r]\times[-H,-\varepsilon]$ is zero.
--
--   This is the lower-half-plane companion to the finite upper contour identity. Together they isolate the two boundary values along the real-axis cut before passage to the keyhole limits.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, finite lower-half-plane contour step in the keyhole argument.

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_div_differentiableAt_of_im_ne_zero
open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_root_lower_rectangle_integral_eq_zero
    (n : ℕ) (a w : ℕ → ℝ) (l r ε H : ℝ)
    (hε : 0 < ε) (hεH : ε ≤ H) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x - H * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - ε * Complex.I)) +
        Complex.I • (∫ y : ℝ in -H..-ε, f (r + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in -H..-ε, f (l + y * Complex.I)) = 0 := by sorry

end WeightedRootIntegralIdentity
