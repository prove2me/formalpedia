-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:15:08.544988+00:00
-- url     : https://prove2.me/theorems/225331b0-7e00-4fe0-98bb-a666d322ccc6
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Inseparable Branch Map comp second Order
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Inseparable Branch Map comp second Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L128-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L128-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_secondOrder
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN) =
      (lpsOriginalRelativeGaussInseparableBranchFrobeniusEquiv N p hNp h4N hN hpN q).symm.toRingHom.comp
        (Ideal.Quotient.mk q) := by sorry
