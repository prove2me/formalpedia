-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_mul_conj_self
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternion.mul_conj_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:39:58.337064+00:00
-- url     : https://prove2.me/theorems/32de228e-39a1-4db6-949b-0a0477f7572d
-- title:
--   LPSQuaternion: mul conj self
-- statement:
--   The right-handed version of the norm identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L74-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L74-L77

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternion.mul_conj_self (t : LPSQuaternion) :
    t * t.conj = lpsScaleQuaternion t.norm 1 := by sorry
