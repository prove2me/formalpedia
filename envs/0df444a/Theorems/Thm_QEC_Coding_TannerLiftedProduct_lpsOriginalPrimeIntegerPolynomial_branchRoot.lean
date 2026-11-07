-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_branchRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_branchRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:29:49.68841+00:00
-- url     : https://prove2.me/theorems/38940b19-da9c-4229-b3a7-071ef454b0c4
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial branch Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial branch Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L176-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean#L176-L184

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_branchRoot (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) (lpsOriginalPrimeBranch p i τ)=0 := by sorry
