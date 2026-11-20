-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeKronecker_afterCoefficientMap
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeKronecker_afterCoefficientMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:56:53.619826+00:00
-- url     : https://prove2.me/theorems/65ee0b95-bd1c-4659-a214-5c8824876489
-- title:
--   Tanner Lifted Product: lps Original Prime Kronecker after Coefficient Map
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Kronecker after Coefficient Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L92-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L92-L101

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeKronecker_afterCoefficientMap
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (f : Polynomial (ZMod p) →+* A) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (f.comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))) =
      (Polynomial.X - Polynomial.C ((f Polynomial.X)^p)) *
        (Polynomial.X^p - Polynomial.C (f Polynomial.X)) := by sorry
