-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:58:35.223424+00:00
-- url     : https://prove2.me/theorems/bb14fee1-deec-4b1d-b5cf-05d8beb696b0
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue integer Polynomial is Unit
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue integer Polynomial is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L30-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondUnits.lean#L30-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_integerPolynomial_isUnit
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) (hP : P ∉ lpsOriginalGaussPrime p) :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    IsUnit (P.eval₂ (Int.castRingHom (LPSOriginalGaussAffineOrder N hN p ⧸ q))
      (lpsOriginalGaussMaximalResidueJ N hN p q)) := by sorry
