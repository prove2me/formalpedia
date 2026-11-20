-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNIntegerFractionEval_X
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNIntegerFractionEval_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:55:56.722867+00:00
-- url     : https://prove2.me/theorems/37641f9f-2b5b-47a8-aa98-8350ad8d89c6
-- title:
--   Tanner Lifted Product: lps Original JNInteger Fraction Eval X
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JNInteger Fraction Eval X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L71-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L71-L76

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNIntegerFractionEval_X (N : ℕ) (hN : 0 < N) :
    lpsOriginalJNIntegerFractionEval N hN Polynomial.X =
      lpsOriginalJNInFractionField N hN := by sorry
