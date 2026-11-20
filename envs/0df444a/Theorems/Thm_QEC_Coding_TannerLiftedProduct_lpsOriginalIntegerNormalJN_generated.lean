-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJN_generated
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJN_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:59:00.736381+00:00
-- url     : https://prove2.me/theorems/8c4be983-53ce-4bf0-97fd-118e0f305544
-- title:
--   Tanner Lifted Product: lps Original Integer Normal JN generated
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Normal JN generated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L70-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L70-L76

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalJN_generated
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerNormalJN N hN).val = lpsOriginalRationalJNElement N hN := by sorry
