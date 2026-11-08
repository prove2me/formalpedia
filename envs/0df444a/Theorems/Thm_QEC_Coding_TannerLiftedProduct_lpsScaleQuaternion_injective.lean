-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:37:16.02134+00:00
-- url     : https://prove2.me/theorems/46ed3825-95ac-4c8b-b2a7-6acdd63d378b
-- title:
--   Tanner Lifted Product: lps Scale Quaternion injective
-- statement:
--   Scaling by a nonzero integer is injective on integral quaternions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L43-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L43-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_injective {s : ℤ} (hs : s ≠ 0) :
    Function.Injective (lpsScaleQuaternion s) := by sorry
