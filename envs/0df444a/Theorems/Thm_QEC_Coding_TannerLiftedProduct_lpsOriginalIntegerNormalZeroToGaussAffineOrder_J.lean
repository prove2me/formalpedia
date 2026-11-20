-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroToGaussAffineOrder_J
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroToGaussAffineOrder_J
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:01:56.45018+00:00
-- url     : https://prove2.me/theorems/5370e0ff-c594-4eaa-a670-aa62a117209c
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Zero To Gauss Affine Order J
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal Zero To Gauss Affine Order J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L163-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L163-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroToGaussAffineOrder_J
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalIntegerNormalZeroToGaussAffineOrder N hN p hpN
      (lpsOriginalIntegerNormalJ N hN) =
      AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) := by sorry
