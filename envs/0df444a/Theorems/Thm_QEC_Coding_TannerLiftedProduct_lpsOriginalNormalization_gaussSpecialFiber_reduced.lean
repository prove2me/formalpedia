-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalization_gaussSpecialFiber_reduced
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalization_gaussSpecialFiber_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:24:42.335568+00:00
-- url     : https://prove2.me/theorems/cd7ecb4d-90b1-4eba-8055-197e97dd08fe
-- title:
--   Tanner Lifted Product: lps Original Normalization gauss Special Fiber reduced
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normalization gauss Special Fiber reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L221-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussSpecialFiber.lean#L221-L227

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
variable (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberBaseFieldAlgebra
local notation "D" => integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN)
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationCommRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationRing
attribute [local instance] QEC.Coding.TannerLiftedProduct.gaussFiberNormalizationSemiring
include hN

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalization_gaussSpecialFiber_reduced (hpN : ¬ p ∣ N) :
    IsReduced (D ⧸ (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p) D)) := by sorry
