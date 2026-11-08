-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_div_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_div_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:36:11.655689+00:00
-- url     : https://prove2.me/theorems/9cb9ea23-ee26-4007-881c-0573c9b86dc1
-- title:
--   Tanner Lifted Product: lps Scale Quaternion div eq
-- statement:
--   Exact coordinate division is inverse to coordinatewise scaling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L29-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L29-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_div_eq
    {s : ℤ} {t : LPSQuaternion} (h : t.CoordinatesDvd s) :
    lpsScaleQuaternion s (lpsQuaternionDiv s t) = t := by sorry
