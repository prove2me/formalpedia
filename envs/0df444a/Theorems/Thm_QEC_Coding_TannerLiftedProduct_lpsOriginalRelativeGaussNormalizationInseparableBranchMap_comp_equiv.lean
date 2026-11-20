-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_equiv
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:59:00.636508+00:00
-- url     : https://prove2.me/theorems/0e8a7bed-f3ef-49ba-819e-6bc6e60b9097
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Inseparable Branch Map comp equiv
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Inseparable Branch Map comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L113-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L113-L126

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationInseparableBranchMap_comp_equiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalRelativeGaussNormalizationInseparableBranchMap N p hNp h4N hN hpN q).comp
      (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).toRingHom =
      lpsOriginalRelativeGaussHeckeInseparableBranchMap N hN p hpN q := by sorry
