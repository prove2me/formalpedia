-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasLPSParity_lpsQuaternionDiv
-- name    : QEC.Coding.TannerLiftedProduct.hasLPSParity_lpsQuaternionDiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:46:05.691586+00:00
-- url     : https://prove2.me/theorems/b6cc0213-2b5f-4e13-9ce9-de94a12d5195
-- title:
--   Tanner Lifted Product: has LPSParity lps Quaternion Div
-- statement:
--   Exact division by an odd scalar preserves the LPS parity class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L213-L235
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean#L213-L235

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.hasLPSParity_lpsQuaternionDiv
    (hpOdd : Odd (p : ℤ)) {t : LPSQuaternion}
    (hdiv : t.CoordinatesDvd (p : ℤ)) (ht : t.HasLPSParity) :
    (lpsQuaternionDiv (p : ℤ) t).HasLPSParity := by sorry
