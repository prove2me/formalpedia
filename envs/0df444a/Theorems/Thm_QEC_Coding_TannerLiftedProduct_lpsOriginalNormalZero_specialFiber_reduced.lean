-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalZero_specialFiber_reduced
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_specialFiber_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:00.392359+00:00
-- url     : https://prove2.me/theorems/9c3a239c-a00a-4cd2-bfd5-9aa0b4e0eed8
-- title:
--   Tanner Lifted Product: lps Original Normal Zero special Fiber reduced
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normal Zero special Fiber reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L230-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSpecialFiberDescent.lean#L230-L239

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalZero_specialFiber_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    IsReduced (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) ⧸
      Ideal.span {(p : integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))}) := by sorry
