-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEncodedCheckEquiv_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsEncodedCheckEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:16:47.227974+00:00
-- url     : https://prove2.me/theorems/01cf1dea-e087-41d1-88c4-00e3f6d89784
-- title:
--   Tanner Lifted Product: lps Encoded Check Equiv apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Encoded Check Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L243-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L243-L245

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113

theorem QEC.Coding.TannerLiftedProduct.lpsEncodedCheckEquiv_apply {q D r r' s : ℕ} [Fact q.Prime] {F : Type}
    (e : Fin s ≃ F) (c : LPSEncodedCheckIndex q D r r' s) :
    lpsEncodedCheckEquiv e c = lpsEncodedCheckDecode e c := by sorry
