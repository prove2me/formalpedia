-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_j
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:15:11.472169+00:00
-- url     : https://prove2.me/theorems/11463d76-364d-4a41-852c-741fca52981c
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Second Order Map j
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Second Order Map j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L85-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L85-L93

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_j
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X)) =
      lpsOriginalRelativeGaussNormalizationSecondJ N p hNp h4N hN := by sorry
