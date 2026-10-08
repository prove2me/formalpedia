-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_offset_integral_jump_eq_im
-- name    : WeightedRootIntegralIdentity.weighted_root_offset_integral_jump_eq_im
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T20:39:33.508584+00:00
-- url     : https://prove2.me/theorems/39898850-fdff-4c66-aeda-592b3330a781
-- title:
--   Finite-height boundary jump as twice an imaginary part
-- statement:
--   For the principal-power weighted-root integrand
--   $$f(z)=\frac{\prod_{i=0}^{n-1}(z-a_i)^{w_i}}{z}$$
--   and any $\varepsilon>0$, one has
--   $$\int_l^r f(x+i\varepsilon)\,dx-\int_l^r f(x-i\varepsilon)\,dx
--   =2i\,\operatorname{Im}\!\left(\int_l^r f(x+i\varepsilon)\,dx\right).$$
--
--   This converts the two-sided finite-height jump into a single upper-half-plane integral, preparing the passage to the real-axis boundary value.
-- source:
--   Conjugation reduction in the keyhole contour argument of K B Dave, Mathematics Stack Exchange, https://math.stackexchange.com/a/4245016.

import Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_upper_lower_conj
open scoped BigOperators Interval ComplexConjugate

namespace WeightedRootIntegralIdentity

theorem weighted_root_offset_integral_jump_eq_im
    (n : ℕ) (a w : ℕ → ℝ) (l r ε : ℝ) (hε : 0 < ε) :
    let f : ℂ → ℂ := fun z =>
      (∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) / z
    (∫ x : ℝ in l..r, f (x + ε * Complex.I)) -
        (∫ x : ℝ in l..r, f (x - ε * Complex.I)) =
      2 * Complex.I *
        ((((∫ x : ℝ in l..r, f (x + ε * Complex.I))).im : ℝ) : ℂ) := by sorry

end WeightedRootIntegralIdentity
