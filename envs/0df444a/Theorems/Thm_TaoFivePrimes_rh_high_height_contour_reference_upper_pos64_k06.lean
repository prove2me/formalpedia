-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_contour_reference_upper_pos64_k06
-- name    : TaoFivePrimes.rh_high_height_contour_reference_upper_pos64_k06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:06:06.77962+00:00
-- url     : https://prove2.me/theorems/ca73f2d9-6ab9-4028-a358-6d47ed28e3ba
-- title:
--   TaoFivePrimes.rh_high_height_contour_reference_upper_pos64_k06
-- statement:
--   Exact integer comparison of2048 proposed80-bit contour coefficients to the128-bit rational reference at start64, order6. Sixty-four independent16-index ordinary kernel checks bound each component difference by2^52. This is finite arithmetic; the analytic accuracy of the rational reference is a separate theorem.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourSpectrumUpperPos64K06

theorem TaoFivePrimes.rh_high_height_contour_reference_upper_pos64_k06 :
  ∀ m:Nat,1 ≤ m ∧ m≤1024 → ∀ positive:Bool,
  let a:=RHHighContourCoefficientData.coefficient ⟨2,by decide⟩ positive m 6
  let b:=RHHighContourCoefficientData.proposed RHHighContourSpectrumUpperPos64K06.rows.flatten positive m
  |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by sorry
