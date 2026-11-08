-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_mul_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:38:18.252289+00:00
-- url     : https://prove2.me/theorems/fba2c355-5e2d-4b98-8605-b39cb5000a91
-- title:
--   Tanner Lifted Product: lps Scale Quaternion mul right
-- statement:
--   Coordinatewise scaling commutes with multiplication on the right.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L60-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L60-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_mul_right
    (s : ℤ) (t u : LPSQuaternion) :
    lpsScaleQuaternion s (t * u) = t * lpsScaleQuaternion s u := by sorry
