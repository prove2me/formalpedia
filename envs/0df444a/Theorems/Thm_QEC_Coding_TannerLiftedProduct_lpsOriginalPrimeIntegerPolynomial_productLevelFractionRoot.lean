-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:00:32.838881+00:00
-- url     : https://prove2.me/theorems/9c468af2-9ed2-44d7-9bcf-cbc101cf5828
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial product Level Fraction Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial product Level Fraction Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L78-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L78-L90

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot
    (N p : ℕ) [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂ (lpsOriginalJNIntegerFractionEval N hN)
      (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp)) = 0 := by sorry
