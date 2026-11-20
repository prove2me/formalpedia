-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:14:46.536143+00:00
-- url     : https://prove2.me/theorems/42074bd4-d59b-43cf-82d4-1834e6329687
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Second Order Map root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Second Order Map root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L68-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L68-L74

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_root
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) =
      lpsOriginalRelativeGaussNormalizationRoot N p hNp h4N hN hpN := by sorry
