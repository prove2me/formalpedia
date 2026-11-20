-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:56.653371+00:00
-- url     : https://prove2.me/theorems/5fdde9e0-3241-4fd5-afbd-032e8b96aff6
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero To Gauss Affine Order JN
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero To Gauss Affine Order JN property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L140-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L140-L161

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroToGaussAffineOrder_JN
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN
      (lpsOriginalIntegerNormalJN N hN) =
      AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p) := by sorry
