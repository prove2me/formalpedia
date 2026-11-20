-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProductLevelCoefficientMap_holomorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProductLevelCoefficientMap_holomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:01:38.25928+00:00
-- url     : https://prove2.me/theorems/2fa08d0c-f854-4756-ae2a-1b2c8898054e
-- title:
--   Tanner Lifted Product: lps Original Integer Product Level Coefficient Map holomorphic
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Product Level Coefficient Map holomorphic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L199-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L199-L219

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProductLevelCoefficientMap_holomorphic
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)]
    (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    (lpsOriginalIntegerNormalToHolomorphic (N*p) (Nat.mul_pos hN hp)).comp
      (lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN hp) =
      lpsOriginalJNIntegerFractionEval N hN := by sorry
