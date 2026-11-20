-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_actualResidueRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_actualResidueRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:29:02.985572+00:00
-- url     : https://prove2.me/theorems/5fdf7124-e2e2-4251-b392-4ef6b1bbb0a0
-- title:
--   Tanner Lifted Product: lps Original Modular Polynomial Mod Fraction actual Residue Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Modular Polynomial Mod Fraction actual Residue Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L65-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L65-L73

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_actualResidueRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalModularPolynomialModFraction N hN p).eval₂
      (lpsOriginalGaussMaximalResidueFractionMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q) = 0 := by sorry
