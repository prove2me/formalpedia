-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_lpsQuaternionDiv_of_prime_pow
-- name    : QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionDiv_of_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:38:14.677449+00:00
-- url     : https://prove2.me/theorems/ac86c82c-5274-4cb9-9bb4-cd88b5e35bf2
-- title:
--   Tanner Lifted Product: norm lps Quaternion Div of prime pow
-- statement:
--   Dividing all coordinates by `p` lowers a norm `p^(n+2)` to `p^n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L80-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L80-L95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionDiv_of_prime_pow
    (hp : p.Prime) {n : ℕ} {t : LPSQuaternion}
    (hdiv : t.CoordinatesDvd (p : ℤ))
    (hnorm : t.norm = (p : ℤ) ^ (n + 2)) :
    (lpsQuaternionDiv (p : ℤ) t).norm = (p : ℤ) ^ n := by sorry
