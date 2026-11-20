-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:38:59.095485+00:00
-- url     : https://prove2.me/theorems/0aa34628-438d-4d64-9d85-365e23745c11
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization First Fiber Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization First Fiber Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L211-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFrobeniusFiber.lean#L211-L230

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Injective (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q) := by sorry
