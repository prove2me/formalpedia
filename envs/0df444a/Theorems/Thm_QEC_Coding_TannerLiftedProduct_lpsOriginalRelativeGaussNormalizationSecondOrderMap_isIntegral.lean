-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_isIntegral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_isIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:41:19.700797+00:00
-- url     : https://prove2.me/theorems/d7750390-ace5-432b-997c-27fe8ad39fca
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Second Order Map is Integral
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Second Order Map is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L232-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L232-L238

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_isIntegral
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).IsIntegral := by sorry
