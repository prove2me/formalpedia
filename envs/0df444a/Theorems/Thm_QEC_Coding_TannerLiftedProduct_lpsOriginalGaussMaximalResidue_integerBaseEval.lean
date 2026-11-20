-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerBaseEval
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_integerBaseEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:05.457325+00:00
-- url     : https://prove2.me/theorems/7901f1b4-949f-41c1-980e-2587d7e8e4d8
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue integer Base Eval
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue integer Base Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L320-L332
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L320-L332

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_integerBaseEval
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    ((Ideal.Quotient.mk q).comp
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p))).comp
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by sorry
