-- Prove2me | Theorems.Thm_Real_enorm_rpow_le_lintegral_deriv_of_eq_zero
-- name    : Real.enorm_rpow_le_lintegral_deriv_of_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T16:48:51.58369+00:00
-- url     : https://prove2.me/theorems/92fc8354-4151-4ac5-a4b9-887f81588eee
-- title:
--   Endpoint power bounded by weighted derivative energy on an interval
-- statement:
--   Let g be a real C¹ function on a closed interval [a,b], with a ≤ b and g(b)=0. For every real r ≥ 1,
--
--   $$|g(a)|^r\le r\int_{(a,b)} |g(t)|^{r-1}|g'(t)|\,dt.$$
--
--   The integral is an extended nonnegative integral. The zero-length interval and exponent one are included. Values of g outside the interval are unrestricted.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, proof of Theorem 3.44, printed p. 72 (normal fundamental theorem, Fubini and Holder step). Anisotropic Holder form of the smooth trace estimate; it is the first half of the derivation of the two-energy bound. Here only C¹ regularity is assumed; this is the regularity used in the normal-ray argument. Supporting interface: finite-interval normal-ray estimate, allowing arbitrary endpoints.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Set
open scoped ENNReal ContDiff
set_option autoImplicit false

theorem Real.enorm_rpow_le_lintegral_deriv_of_eq_zero (r : ℝ) (hr : 1 ≤ r) (g : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hg : ContDiffOn ℝ 1 g (Icc a b)) (hb : g b = 0) :
    ‖g a‖ₑ ^ r ≤ ENNReal.ofReal r *
      ∫⁻ t in Ioo a b, ‖g t‖ₑ ^ (r - 1) * ‖deriv g t‖ₑ := by sorry
