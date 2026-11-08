-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_conj_mul
-- name    : QEC.Coding.TannerLiftedProduct.LPSQuaternion.conj_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:47:45.194253+00:00
-- url     : https://prove2.me/theorems/02aed095-c0df-4c8e-be5e-58103b400aa5
-- title:
--   LPSQuaternion: conj mul
-- statement:
--   Quaternion conjugation reverses multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRing.lean#L139-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRing.lean#L139-L144

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.TransferInstance
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRing
set_option autoImplicit false
open scoped MatrixGroups Quaternion
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.LPSQuaternion.conj_mul (t u : LPSQuaternion) :
    (t * u).conj = u.conj * t.conj := by sorry
