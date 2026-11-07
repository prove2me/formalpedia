-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalInfinity_primeIdeal_radical
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalInfinity_primeIdeal_radical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:44.203476+00:00
-- url     : https://prove2.me/theorems/95810923-1405-432f-9a5f-00a9aec546c5
-- title:
--   Tanner Lifted Product: lps Original Normal Infinity prime Ideal radical
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normal Infinity prime Ideal radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalSpecialFiber.lean#L284-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalSpecialFiber.lean#L284-L350

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalInfinity_primeIdeal_radical
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    (Ideal.span {(p : integralClosure (Polynomial ℤ)
      (lpsOriginalGeneratedFunctionFieldQ N hN))}).IsRadical := by sorry
