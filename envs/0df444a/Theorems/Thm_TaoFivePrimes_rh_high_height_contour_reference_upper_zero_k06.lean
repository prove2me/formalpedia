-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_zero_k06
-- name    : TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:04:52.355054+00:00
-- url     : https://prove2.me/theorems/c5f4bb6d-95a4-4241-8113-455cb7bbb09f
-- title:
--   TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k06
-- statement:
--   Exact integer comparison of2048 proposed80-bit contour coefficients to the128-bit rational reference at start0, order6. Sixty-four independent16-index ordinary kernel checks bound each component difference by2^52. This is finite arithmetic; the analytic accuracy of the rational reference is a separate theorem.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperZeroK06

theorem TaoFivePrimes.rh_high_height_contour_reference_upper_zero_k06 :
  ∀ m:Nat,1 ≤ m ∧ m≤1024 → ∀ positive:Bool,
  let a:=RHHighContourCoefficientData.coefficient ⟨1,by decide⟩ positive m 6
  let b:=RHHighContourCoefficientData.proposed RHHighContourSpectrumUpperZeroK06.rows.flatten positive m
  |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by sorry
