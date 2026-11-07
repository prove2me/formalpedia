-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_fractionProduct
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_fractionProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:31:56.567067+00:00
-- url     : https://prove2.me/theorems/82d532b1-8e99-4f4e-87fd-a605e1b5ca56
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial fraction Product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial fraction Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L225-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L225-L256

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_fractionProduct (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      ((algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalZ)=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalPrimeFractionBranch p i)) := by sorry
