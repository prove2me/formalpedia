-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueFractionMap_X
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueFractionMap_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:29:45.078922+00:00
-- url     : https://prove2.me/theorems/bb66eeb0-032c-45ff-b0db-aba5413e88c5
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue Fraction Map X
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue Fraction Map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L18-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L18-L27

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueFractionMap_X
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    lpsOriginalGaussMaximalResidueFractionMap N hN p q
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) =
      lpsOriginalGaussMaximalResidueJ N hN p q := by sorry
