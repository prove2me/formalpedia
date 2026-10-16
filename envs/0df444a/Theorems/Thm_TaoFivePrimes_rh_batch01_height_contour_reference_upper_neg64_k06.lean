-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_reference_upper_neg64_k06
-- name    : TaoFivePrimes.rh_batch01_height_contour_reference_upper_neg64_k06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:13:46.865533+00:00
-- url     : https://prove2.me/theorems/828b30d2-04d2-4805-a4bb-055a28f377c0
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_reference_upper_neg64_k06
-- statement:
--   Exact integer comparison of2048 proposed80-bit contour coefficients to the128-bit rational reference at start-64, order6. Sixty-four independent16-index ordinary kernel checks bound each component difference by2^52. This is finite arithmetic; the analytic accuracy of the rational reference is a separate theorem.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K06

theorem TaoFivePrimes.rh_batch01_height_contour_reference_upper_neg64_k06 :
  ∀ m:Nat,1 ≤ m ∧ m≤1024 → ∀ positive:Bool,
  let a:=RHBatch01ContourCoefficientData.coefficient ⟨0,by decide⟩ positive m 6
  let b:=RHBatch01ContourCoefficientData.proposed RHBatch01ContourSpectrumUpperNeg64K06.rows.flatten positive m
  |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by sorry
