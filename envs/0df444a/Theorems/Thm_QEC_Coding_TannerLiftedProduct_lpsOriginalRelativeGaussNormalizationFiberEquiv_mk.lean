-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberEquiv_mk
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:57.322451+00:00
-- url     : https://prove2.me/theorems/98915707-b7ad-4608-886f-dea8f70c335d
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Fiber Equiv mk
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Fiber Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L114-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L114-L134

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberEquiv_mk
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (x : LPSOriginalRelativeGaussHeckeOrder N hN p) :
    lpsOriginalRelativeGaussNormalizationFiberEquiv N p hNp h4N hN hpN q
      (Ideal.Quotient.mk _
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN x)) =
      lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q (Ideal.Quotient.mk _ x) := by sorry
