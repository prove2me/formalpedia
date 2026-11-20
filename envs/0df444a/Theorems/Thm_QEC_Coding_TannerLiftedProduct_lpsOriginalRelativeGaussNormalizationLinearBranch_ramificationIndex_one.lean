-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationLinearBranch_ramificationIndex_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranch_ramificationIndex_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:33:09.573044+00:00
-- url     : https://prove2.me/theorems/01e529d1-d65b-47c5-b8e3-1d861bb33465
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Linear Branch ramification Index one
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Linear Branch ramification Index one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L309-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L309-L330

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationLinearBranch_ramificationIndex_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).ramificationIdx (LPSOriginalGaussAffineOrder N hN p) = 1 := by sorry
