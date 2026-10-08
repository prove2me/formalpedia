-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_combined_rectangle_boundary_identity
-- name    : WeightedRootIntegralIdentity.weighted_root_combined_rectangle_boundary_identity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T15:13:41.456974+00:00
-- url     : https://prove2.me/theorems/bb68834b-a002-41a5-9def-1b12ff1fa552
-- title:
--   Combined upper and lower truncated-boundary identity
-- statement:
--   For
--   $$f(z)=\frac{\prod_{i=0}^{n-1}(z-a_i)^{w_i}}{z},$$
--   let $0<\varepsilon\le H$. Subtracting the lower boundary value of $f$ at height $-\varepsilon$ from its upper boundary value at height $\varepsilon$, and integrating from $l$ to $r$, equals the corresponding difference at heights $\pm H$ together with the oriented integrals along the four vertical truncation edges.
--
--   This identity combines Cauchy–Goursat on the upper and lower rectangles and isolates the jump across the real-axis branch cut. It is the finite precursor of the weighted-root keyhole boundary formula.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, combination of the upper and lower finite contour equations.

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_upper_rectangle_integral_eq_zero
import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_lower_rectangle_integral_eq_zero
open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_root_combined_rectangle_boundary_identity
    (n : ℕ) (a w : ℕ → ℝ) (l r ε H : ℝ)
    (hε : 0 < ε) (hεH : ε ≤ H) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x + ε * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - ε * Complex.I)) =
      (∫ x : ℝ in l..r, f (x + H * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - H * Complex.I)) -
        Complex.I • (∫ y : ℝ in ε..H, f (r + y * Complex.I)) +
        Complex.I • (∫ y : ℝ in ε..H, f (l + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in -H..-ε, f (r + y * Complex.I)) +
        Complex.I • (∫ y : ℝ in -H..-ε, f (l + y * Complex.I)) := by sorry

end WeightedRootIntegralIdentity
