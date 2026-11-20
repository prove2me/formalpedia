-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationRoot_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationRoot_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:31:15.277685+00:00
-- url     : https://prove2.me/theorems/12fc7d66-244b-4106-9f14-81fbd1522e08
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Root coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Root coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L73-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L73-L78

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationRoot_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN).val.val =
      lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by sorry
