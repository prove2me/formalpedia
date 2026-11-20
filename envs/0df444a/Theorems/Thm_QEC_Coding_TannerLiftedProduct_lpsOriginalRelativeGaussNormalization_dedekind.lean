-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_dedekind
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_dedekind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:32:06.608299+00:00
-- url     : https://prove2.me/theorems/2b97264d-b9cf-4f24-9e66-7afdc48c98a2
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization dedekind
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization dedekind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L186-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean#L186-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_dedekind
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    IsDedekindDomain (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by sorry
