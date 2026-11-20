-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:56:55.032005+00:00
-- url     : https://prove2.me/theorems/1a166c0f-f2b7-4026-9dba-98744e1fea55
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial product Level Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial product Level Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L30-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L30-L37

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelRoot
    (N p : ℕ) [NeZero p] (hN : 0 < N) (hp : 0 < p) (τ : ℍ) :
    (lpsOriginalIntegerPolynomial p hp).eval₂
      ((Polynomial.evalRingHom (lpsOriginalJDilated N hN τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)))
      (lpsOriginalJDilated (N*p) (Nat.mul_pos hN hp) τ) = 0 := by sorry
