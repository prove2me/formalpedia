-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_real_reference_zero
-- name    : TaoFivePrimes.rh_batch01_height_real_reference_zero
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:55:56.043991+00:00
-- url     : https://prove2.me/theorems/c0ac26a6-8f97-44b0-b11f-0ec4b266398a
-- title:
--   TaoFivePrimes.rh_batch01_height_real_reference_zero
-- statement:
--   Exact128-bit eighth-root products and80-bit rounding for all2048 nonconstant coefficients in the proposed real spectrum, with finite component magnitude bounds and an exact constant coefficient. Requires a separate analytic enclosure before proving polynomial or zeta signs.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHBatch01RealSpectrumZero

theorem TaoFivePrimes.rh_batch01_height_real_reference_zero :
 (RHBatch01RealSpectrumZero.rows.flatten[0]?).getD 0=RHBatch01FourierPolynomial.word 0 ∧
 ∀m:Nat,1 ≤ m ∧ m≤1024 → ∀positive:Bool,
  let p:=RHHighContourVector.coefficient RHBatch01RealSpectrumZero.rows.flatten positive m
  let q:=RHBatch01ContourCoefficientData.mul (RHBatch01ContourCoefficientData.inputCoefficient m positive)
    (RHHighContourUnit.pair (RHBatch01ContourCoefficientData.rootIndex ⟨1,by decide⟩ positive m))
  p=(q.1/(2:Int)^48,q.2/(2:Int)^48) ∧ |p.1|+|p.2|≤(2:Int)^80 := by sorry
