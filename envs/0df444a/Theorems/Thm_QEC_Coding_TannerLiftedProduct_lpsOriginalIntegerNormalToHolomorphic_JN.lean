-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalToHolomorphic_JN
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalToHolomorphic_JN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:00:56.859187+00:00
-- url     : https://prove2.me/theorems/edb9b823-d0fc-47a9-bcb3-fd704aaf1267
-- title:
--   Tanner Lifted Product: lps Original Integer Normal To Holomorphic JN
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal To Holomorphic JN property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L157-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeIntegralHeckeRelation.lean#L157-L161

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalToHolomorphic_JN
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalToHolomorphic N hN (lpsOriginalIntegerNormalJN N hN) =
      lpsOriginalJNInFractionField N hN := by sorry
