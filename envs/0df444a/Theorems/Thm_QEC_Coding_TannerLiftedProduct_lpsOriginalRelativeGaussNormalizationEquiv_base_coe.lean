-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationEquiv_base_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationEquiv_base_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:22:55.919433+00:00
-- url     : https://prove2.me/theorems/df766765-7b49-4cf0-9f32-ce54410bf3a0
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Equiv base coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Equiv base coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalization.lean#L456-L485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalization.lean#L456-L485

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationEquiv_base_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (c : LPSOriginalGaussAffineOrder N hN p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    ((lpsOriginalRelativeGaussNormalizationEquiv N p hNp h4N hN hpN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)).val.val) =
      (lpsOriginalGaussAffineToGenerated N hN p c).val := by sorry
