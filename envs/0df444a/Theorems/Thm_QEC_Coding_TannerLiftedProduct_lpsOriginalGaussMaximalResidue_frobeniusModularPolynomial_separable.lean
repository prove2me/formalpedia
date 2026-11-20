-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:38:38.584179+00:00
-- url     : https://prove2.me/theorems/6e5ffec5-82de-4015-8164-742c98268932
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue frobenius Modular Polynomial separable
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue frobenius Modular Polynomial separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondBranches.lean#L112-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondBranches.lean#L112-L128

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidue_frobeniusModularPolynomial_separable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    ((lpsOriginalIntegerPolynomial N hN).map
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        ((lpsOriginalGaussMaximalResidueJ N hN p q)^p))).Separable := by sorry
