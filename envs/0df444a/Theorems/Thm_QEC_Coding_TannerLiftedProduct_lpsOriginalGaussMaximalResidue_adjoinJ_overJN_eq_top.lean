-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_adjoinJ_overJN_eq_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_adjoinJ_overJN_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:35.92795+00:00
-- url     : https://prove2.me/theorems/68ed5dc6-b05a-461b-8bb6-3f50d3c281d1
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue adjoin J over JN eq top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue adjoin J over JN eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L334-L371
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L334-L371

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_adjoinJ_overJN_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q).toAlgebra
    IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
      {lpsOriginalGaussMaximalResidueJ N hN p q} = ⊤ := by sorry
