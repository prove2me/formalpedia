-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_reference_neg64
-- name    : TaoFivePrimes.rh_high_height_real_reference_neg64
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T08:56:03.09354+00:00
-- url     : https://prove2.me/theorems/19c549a3-95c6-47cf-8357-8b12aa561260
-- title:
--   TaoFivePrimes.rh_high_height_real_reference_neg64
-- statement:
--   Exact128-bit eighth-root products and80-bit rounding for all2048 nonconstant coefficients in the proposed real spectrum, with finite component magnitude bounds and an exact constant coefficient. Requires a separate analytic enclosure before proving polynomial or zeta signs.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumNeg64

theorem TaoFivePrimes.rh_high_height_real_reference_neg64 :
 (RHHighRealSpectrumNeg64.rows.flatten[0]?).getD 0=RHHighFourierPolynomial.word 0 ∧
 ∀m:Nat,1 ≤ m ∧ m≤1024 → ∀positive:Bool,
  let p:=RHHighContourVector.coefficient RHHighRealSpectrumNeg64.rows.flatten positive m
  let q:=RHHighContourCoefficientData.mul (RHHighContourCoefficientData.inputCoefficient m positive)
    (RHHighContourUnit.pair (RHHighContourCoefficientData.rootIndex ⟨0,by decide⟩ positive m))
  p=(q.1/(2:Int)^48,q.2/(2:Int)^48) ∧ |p.1|+|p.2|≤(2:Int)^80 := by sorry
