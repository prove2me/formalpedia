-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveQuaternionPSL_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionPSL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:06.379781+00:00
-- url     : https://prove2.me/theorems/c620fd71-a6fc-4222-b519-ac6d4ad918a4
-- title:
--   Tanner Lifted Product: lps Effective Quaternion PSL eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Effective Quaternion PSL eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L83-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L83-L87

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveQuaternionPSL_eq (a : LPSResiduePrime p)
    (t : LPSQuaternion) (ht : t.norm = p) :
    lpsEffectiveQuaternionPSL a t ht = lpsQuaternionPSL a t ht := by sorry
