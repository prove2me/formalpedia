-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProductLevelCoefficientMap_X
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProductLevelCoefficientMap_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:00:49.496034+00:00
-- url     : https://prove2.me/theorems/e21b99f6-fe56-4be6-aa23-96ec4fce2a58
-- title:
--   Tanner Lifted Product: lps Original Integer Product Level Coefficient Map X
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Product Level Coefficient Map X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L187-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L187-L197

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProductLevelCoefficientMap_X
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp Polynomial.X =
      lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
        (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
        (lpsOriginalIntegerNormalJN N hN) := by sorry
