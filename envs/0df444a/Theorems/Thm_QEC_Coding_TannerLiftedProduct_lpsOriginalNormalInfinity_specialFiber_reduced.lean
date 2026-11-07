-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalInfinity_specialFiber_reduced
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalInfinity_specialFiber_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:29:09.163863+00:00
-- url     : https://prove2.me/theorems/f11b2326-46f0-4f06-a5ab-b52e468b070f
-- title:
--   Tanner Lifted Product: lps Original Normal Infinity special Fiber reduced
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normal Infinity special Fiber reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalSpecialFiber.lean#L352-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalSpecialFiber.lean#L352-L361

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalInfinity_specialFiber_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    IsReduced (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) ⧸
      Ideal.span {(p : integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))}) := by sorry
