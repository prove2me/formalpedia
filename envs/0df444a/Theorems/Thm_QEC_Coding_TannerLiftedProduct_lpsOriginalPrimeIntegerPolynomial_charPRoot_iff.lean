-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_charPRoot_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_charPRoot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:23:59.904527+00:00
-- url     : https://prove2.me/theorems/c2eb656d-ae1d-4960-86a7-02a4a8810d86
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial char PRoot iff
-- statement:
--   Reduction of any literal prime modular root in a characteristic-p domain
--   has the two genuine Frobenius alternatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L237-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L237-L251

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_charPRoot_iff
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] (j y : A) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom A) j) y = 0 ↔
      y = j^p ∨ y^p = j := by sorry
