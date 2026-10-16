-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_reference_upper_neg64_k04
-- name    : TaoFivePrimes.rh_batch01_height_contour_reference_upper_neg64_k04
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T23:43:32.955269+00:00
-- url     : https://prove2.me/theorems/61511e73-4f7e-4df3-9e17-d6eeb2c5cd91
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_reference_upper_neg64_k04
-- statement:
--   Exact integer comparison of2048 proposed80-bit contour coefficients to the128-bit rational reference at start-64, order4. Sixty-four independent16-index ordinary kernel checks bound each component difference by2^52. This is finite arithmetic; the analytic accuracy of the rational reference is a separate theorem.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
import Definitions.Def_TaoFivePrimes_RHBatch01ContourSpectrumUpperNeg64K04

theorem TaoFivePrimes.rh_batch01_height_contour_reference_upper_neg64_k04 :
  ∀ m:Nat,1 ≤ m ∧ m≤1024 → ∀ positive:Bool,
  let a:=RHBatch01ContourCoefficientData.coefficient ⟨0,by decide⟩ positive m 4
  let b:=RHBatch01ContourCoefficientData.proposed RHBatch01ContourSpectrumUpperNeg64K04.rows.flatten positive m
  |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52 := by sorry
