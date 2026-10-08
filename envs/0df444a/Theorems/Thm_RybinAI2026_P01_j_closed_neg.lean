-- Prove2me | Theorems.Thm_RybinAI2026_P01_j_closed_neg
-- name    : RybinAI2026.P01.j_closed_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T05:24:33.347361+00:00
-- url     : https://prove2.me/theorems/e520a9a5-6230-405b-a9f8-7a3c142d4e8d
-- title:
--   Closed form of the J-profile on (-1,0) via artanh
-- statement:
--   For -1<c<0, the integral over [0,1] of 1/(1+c*t^2) equals artanh(sqrt(-c))/sqrt(-c).
-- source:
--   P01 synthesis 2026-10-04, Agent A commuting-planar programme Lemma L2c Step 1 negative side; draft l2c_closed_neg_DRAFT.lean (sorry-free fragment).

import Mathlib
set_option autoImplicit false
open MeasureTheory
open intervalIntegral

namespace RybinAI2026.P01

/-- For `-1 < c < 0`, `j(c) = artanh(sqrt(-c))/sqrt(-c)` where `j(c) = integral t in 0..1, (1+c*t^2)^{-1}`, by partial fractions and linear substitutions. This is Step 1 (negative side) for Lemma L2c of the commuting-planar programme. -/
theorem j_closed_neg (c : ℝ) (hc1 : -1 < c) (hc0 : c < 0) :
    (∫ t in (0 : ℝ)..1, ((1 : ℝ) + c * t ^ 2)⁻¹)
      = Real.artanh (Real.sqrt (-c)) / Real.sqrt (-c) := by sorry

end RybinAI2026.P01
