-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:15:37.652482+00:00
-- url     : https://prove2.me/theorems/e7a40216-d0ba-46bf-b8c4-6fc3f2e6cf93
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Second Order Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Second Order Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L230-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L230-L248

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_injective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) := by sorry
