-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroGauss_localization
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroGauss_localization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:27:33.910455+00:00
-- url     : https://prove2.me/theorems/cee5f8ea-5834-4387-9fe5-55b989b3e328
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero Gauss localization
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero Gauss localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L152-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L152-L197

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime lpsOriginalGaussPrime_principal

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroGauss_localization
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    let := (lpsOriginalIntegerNormalZeroToGaussNormalization N hN p).toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
        (lpsOriginalGaussPrime p).primeCompl)
      (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by sorry
