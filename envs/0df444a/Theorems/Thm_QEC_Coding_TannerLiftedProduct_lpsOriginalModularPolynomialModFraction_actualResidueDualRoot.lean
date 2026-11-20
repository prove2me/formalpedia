-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularPolynomialModFraction_actualResidueDualRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_actualResidueDualRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:17.483253+00:00
-- url     : https://prove2.me/theorems/45226c98-c075-406b-9c03-af802ae8008e
-- title:
--   Tanner Lifted Product: lps Original Modular Polynomial Mod Fraction actual Residue Dual Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Modular Polynomial Mod Fraction actual Residue Dual Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L256-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L256-L264

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularPolynomialModFraction_actualResidueDualRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalModularPolynomialModFraction N hN p).eval₂
      (lpsOriginalGaussMaximalResidueJN_FractionMap N hN p hpN q)
      (lpsOriginalGaussMaximalResidueJ N hN p q) = 0 := by sorry
