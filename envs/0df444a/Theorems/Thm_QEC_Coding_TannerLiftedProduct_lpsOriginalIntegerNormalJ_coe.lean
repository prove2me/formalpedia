-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJ_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJ_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:13.775075+00:00
-- url     : https://prove2.me/theorems/4ccf0e6a-436f-4305-9d31-b1c1021886fe
-- title:
--   Tanner Lifted Product: lps Original Integer Normal J coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal J coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L61-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L61-L68

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJ_coe
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalToHolomorphic N hN (lpsOriginalIntegerNormalJ N hN) =
      lpsOriginalJInFractionField := by sorry
