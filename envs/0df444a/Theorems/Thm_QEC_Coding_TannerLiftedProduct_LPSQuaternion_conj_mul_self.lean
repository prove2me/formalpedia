-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_conj_mul_self
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternion.conj_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:37:42.368985+00:00
-- url     : https://prove2.me/theorems/dc3137d5-e5d1-4fef-b9f7-65029e773a4c
-- title:
--   LPSQuaternion: conj mul self
-- statement:
--   Quaternion conjugation times the original quaternion is the central
--   scalar given by its reduced norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L68-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L68-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternion.conj_mul_self (t : LPSQuaternion) :
    t.conj * t = lpsScaleQuaternion t.norm 1 := by sorry
