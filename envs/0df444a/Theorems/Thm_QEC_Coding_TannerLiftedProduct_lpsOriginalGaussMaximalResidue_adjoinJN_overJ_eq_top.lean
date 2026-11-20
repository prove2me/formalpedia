-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:30:45.193264+00:00
-- url     : https://prove2.me/theorems/46384706-6ec2-49c2-b62e-779b318b067c
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue adjoin JN over J eq top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue adjoin JN over J eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L90-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L90-L127

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_adjoinJN_overJ_eq_top
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    IntermediateField.adjoin (FractionRing (Polynomial (ZMod p)))
      {lpsOriginalGaussMaximalResidueJN N hN p q} = ⊤ := by sorry
