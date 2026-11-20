-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJ_generated
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJ_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:58:48.531175+00:00
-- url     : https://prove2.me/theorems/358bf97a-b347-4819-8e5f-cd037b10c41f
-- title:
--   Tanner Lifted Product: lps Original Integer Normal J generated
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal J generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L50-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L50-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJ_generated
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerNormalJ N hN).val = lpsOriginalRationalJElement N hN := by sorry
