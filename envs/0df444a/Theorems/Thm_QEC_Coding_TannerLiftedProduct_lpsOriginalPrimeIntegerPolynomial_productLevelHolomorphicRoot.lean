-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelHolomorphicRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelHolomorphicRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:56:50.097185+00:00
-- url     : https://prove2.me/theorems/fb76f9c5-a918-424e-8896-57d46eac0e10
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial product Level Holomorphic Root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Integer Polynomial product Level Holomorphic Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L39-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L39-L64

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelHolomorphicRoot
    (N p : ℕ) [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂ (lpsOriginalJNHolomorphicEvalZ N hN)
      (lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp)) = 0 := by sorry
