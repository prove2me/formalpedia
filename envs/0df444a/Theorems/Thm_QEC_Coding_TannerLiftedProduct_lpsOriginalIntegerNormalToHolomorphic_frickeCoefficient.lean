-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalToHolomorphic_frickeCoefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalToHolomorphic_frickeCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:26.958173+00:00
-- url     : https://prove2.me/theorems/53a23a57-a2ee-49aa-893d-2b4abb41511a
-- title:
--   Tanner Lifted Product: lps Original Integer Normal To Holomorphic fricke Coefficient
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal To Holomorphic fricke Coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L163-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L163-L176

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalToHolomorphic_frickeCoefficient
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalToHolomorphic N hN).comp
      (lpsOriginalIntegerFrickeCoefficientMap N hN) =
      lpsOriginalJNIntegerFractionEval N hN := by sorry
