-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalBaseCoefficientMap_holomorphic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalBaseCoefficientMap_holomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:40.378334+00:00
-- url     : https://prove2.me/theorems/0214fe24-dc5b-4a6b-b1fc-2ae167facae7
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Base Coefficient Map holomorphic
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Base Coefficient Map holomorphic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L31-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L31-L48

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalBaseCoefficientMap_holomorphic
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalIntegerNormalToHolomorphic N hN).comp
      (lpsOriginalIntegerNormalBaseCoefficientMap N hN) =
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalZ := by sorry
