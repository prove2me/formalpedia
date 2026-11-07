-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_conj_mem_lpsQuaternionShell_iff
-- name    : QEC.Coding.TannerLiftedProduct.conj_mem_lpsQuaternionShell_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:33:33.296663+00:00
-- url     : https://prove2.me/theorems/64f5da9a-ef87-493a-b8eb-b407cc9f80e4
-- title:
--   Tanner Lifted Product: conj mem lps Quaternion Shell iff
-- statement:
--   The Tanner Lifted Product construction uses the conj mem lps Quaternion Shell iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L127-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionShell.lean#L127-L131

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.conj_mem_lpsQuaternionShell_iff
    {p : ℕ} (hp : 0 < p) (t : LPSQuaternion) :
    t.conj ∈ lpsQuaternionShell p ↔ t ∈ lpsQuaternionShell p := by sorry
