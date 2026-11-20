-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:01:42.715186+00:00
-- url     : https://prove2.me/theorems/62484f01-c0b4-4bb4-b0af-61a14f529882
-- title:
--   Tanner Lifted Product: lps Original Prime Integer Polynomial product Level Normal Root
-- statement:
--   The literal prime modular equation holds inside the same normalized
--   original integral chart at product level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L223-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L223-L233

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerPolynomial p hp).eval₂
      (lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp)
      (lpsOriginalIntegerNormalJN (N*p) (Nat.mul_pos hN hp)) = 0 := by sorry
