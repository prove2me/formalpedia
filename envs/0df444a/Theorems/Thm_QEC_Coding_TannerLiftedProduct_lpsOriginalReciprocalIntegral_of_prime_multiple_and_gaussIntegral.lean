-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalIntegral_of_prime_multiple_and_gaussIntegral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalIntegral_of_prime_multiple_and_gaussIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:28.212185+00:00
-- url     : https://prove2.me/theorems/ec97ddd3-f614-4c9a-9afa-bb1a44e9aab5
-- title:
--   Tanner Lifted Product: lps Original Reciprocal Integral of prime multiple and gauss Integral
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Reciprocal Integral of prime multiple and gauss Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalSpecialFiber.lean#L215-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalSpecialFiber.lean#L215-L262

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalIntegral_of_prime_multiple_and_gaussIntegral
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
    ∀ y : lpsOriginalGeneratedFunctionFieldQ N hN,
      IsIntegral (Polynomial ℤ) ((p : lpsOriginalGeneratedFunctionFieldQ N hN)*y) →
      IsIntegral (LPSOriginalGaussBase p) y → IsIntegral (Polynomial ℤ) y := by sorry
