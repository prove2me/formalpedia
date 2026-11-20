-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationEquiv_root_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationEquiv_root_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:26.707261+00:00
-- url     : https://prove2.me/theorems/0a648058-94fc-4e60-b4b6-af56b58bcb56
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Equiv root coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Equiv root coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalization.lean#L424-L453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalization.lean#L424-L453

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationEquiv_root_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    ((lpsOriginalRelativeGaussNormalizationEquiv N p hNp h4N hN hpN
      (AdjoinRoot.root (lpsOriginalRelativeGaussHeckePolynomial N hN p))).val.val) =
      lpsOriginalJNInFractionField (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by sorry
