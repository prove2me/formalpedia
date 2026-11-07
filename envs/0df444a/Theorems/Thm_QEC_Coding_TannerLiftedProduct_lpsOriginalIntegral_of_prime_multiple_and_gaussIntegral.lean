-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegral_of_prime_multiple_and_gaussIntegral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegral_of_prime_multiple_and_gaussIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:25:52.849537+00:00
-- url     : https://prove2.me/theorems/47206dc3-c5c2-43ca-b9cf-92b11a5dca13
-- title:
--   Tanner Lifted Product: lps Original Integral of prime multiple and gauss Integral
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integral of prime multiple and gauss Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L114-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L114-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Prime.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring verticalPrimeJAlgebra
  verticalPrimeBaseFieldAlgebra verticalPrimeNormalCommRing verticalPrimeNormalRing
  verticalPrimeNormalSemiring

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegral_of_prime_multiple_and_gaussIntegral
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    ∀ y : lpsOriginalGeneratedFunctionFieldQ N hN,
      IsIntegral (Polynomial ℤ) ((p : lpsOriginalGeneratedFunctionFieldQ N hN)*y) →
      IsIntegral (LPSOriginalGaussBase p) y → IsIntegral (Polynomial ℤ) y := by sorry
