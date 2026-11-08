-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseQubitEquiv_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseQubitEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:12:43.521519+00:00
-- url     : https://prove2.me/theorems/b19cda2b-9891-4be8-8414-b795abefe9f1
-- title:
--   Tanner Lifted Product: lps Sparse Qubit Equiv apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse Qubit Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L278-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L278-L280

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseQubitEquiv_apply {q D r r' : ℕ} [Fact q.Prime]
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseQubitEquiv qubit = lpsSparseQubitDecode qubit := by sorry
