-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:15:33.118173+00:00
-- url     : https://prove2.me/theorems/55a0969d-a99d-4215-828e-18909c14dab4
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Second Order Map generated Diagram
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Second Order Map generated Diagram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L176-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L176-L228

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationSecondOrderMap_generatedDiagram
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ a : LPSOriginalGaussAffineOrder N hN p,
      (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN a).val =
        lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)
          (lpsOriginalGaussAffineToGenerated N hN p a) := by sorry
