-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_mul_left
-- name    : QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_mul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:37:52.663804+00:00
-- url     : https://prove2.me/theorems/2e2e6e68-e8c4-43a0-82df-34058f44091b
-- title:
--   Tanner Lifted Product: lps Scale Quaternion mul left
-- statement:
--   Coordinatewise scaling commutes with multiplication on the left.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L53-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L53-L57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_mul_left
    (s : ℤ) (t u : LPSQuaternion) :
    lpsScaleQuaternion s (t * u) = lpsScaleQuaternion s t * u := by sorry
