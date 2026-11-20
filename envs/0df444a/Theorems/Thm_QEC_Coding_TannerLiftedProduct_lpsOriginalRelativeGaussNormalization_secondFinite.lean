-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondFinite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:40:27.463784+00:00
-- url     : https://prove2.me/theorems/22e74847-1969-4cb9-93b9-08f72ff40504
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization second Finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization second Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L215-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L215-L230

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondFinite
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationSecondOrder_algebra N p hNp h4N hN hpN
    Module.Finite (LPSOriginalGaussAffineOrder N hN p)
      (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by sorry
