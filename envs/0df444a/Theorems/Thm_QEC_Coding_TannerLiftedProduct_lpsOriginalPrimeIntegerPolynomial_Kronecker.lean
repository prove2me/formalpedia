-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_Kronecker
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_Kronecker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:34:00.846676+00:00
-- url     : https://prove2.me/theorems/b4e592fe-f9f3-4aee-a350-368830c1f32a
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial Kronecker
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial Kronecker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L53-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeKronecker.lean#L53-L63

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_Kronecker (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))=
      (Polynomial.X-Polynomial.C ((Polynomial.X : Polynomial (ZMod p))^p)) *
        (Polynomial.X^p-Polynomial.C (Polynomial.X : Polynomial (ZMod p))) := by sorry
