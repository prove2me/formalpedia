-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelResidueRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelResidueRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:57:50.387455+00:00
-- url     : https://prove2.me/theorems/955227e6-e121-4bfa-9ebe-d4f3677f8549
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial product Level Residue Root
-- statement:
--   Every actual characteristic-p domain image of the normalized original
--   product-level chart satisfies one of the two Frobenius relations. This is a
--   pointwise residue identity; it does not assert a scheme cycle equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L256-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L256-L290

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelResidueRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (h4N : 4 ∣ N) (hN : 0 < N)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra (ZMod p) A]
    (q : lpsOriginalIntegerNormalZeroChart (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos) →+* A) :
    let j := q (lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
        (lpsOriginalIntegerNormalJN N hN))
    let y := q (lpsOriginalIntegerNormalJN (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    y = j^p ∨ y^p = j := by sorry
