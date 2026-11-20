-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFrickePullback_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFrickePullback_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:40:13.21761+00:00
-- url     : https://prove2.me/theorems/f2e8cfae-134c-4860-b8a7-8b014e650b35
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Fricke Pullback coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Fricke Pullback coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L118-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussFricke.lean#L118-L125

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondResidueDegrees
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFrickePullback_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (x : LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussNormalizationFrickePullback N p hNp h4N hN hpN x).val =
      lpsOriginalRationalFrickePullback (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos) x.val := by sorry
