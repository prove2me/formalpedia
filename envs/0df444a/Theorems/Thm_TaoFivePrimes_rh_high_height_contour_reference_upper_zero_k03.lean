-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k03
-- name    : TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k03
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:38:42.592786+00:00
-- url     : https://prove2.me/theorems/f4d1ed66-7ff2-42a9-8220-5dc369a64c2c
-- title:
--   TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k03
-- statement:
--   Exact integer comparison of2048 proposed80-bit contour coefficients to the128-bit rational reference at start0, order3. Sixty-four independent16-index ordinary kernel checks bound each component difference by2^52. This is finite arithmetic; the analytic accuracy of the rational reference is a separate theorem.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK03

theorem TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k03 :
  ∀ m:Nat,1 ≤ m ∧ m≤1024 → ∀ positive:Bool,
  let a:=RHHighContourCoefficientData.coefficient ⟨1,by decide⟩ positive m 3
  let b:=RHHighContourCoefficientData.proposed RHHighContourSpectrumUpperZeroK03.rows.flatten positive m
  |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by sorry
