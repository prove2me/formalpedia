-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionDiv_mul_conj_mul_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuaternionDiv_mul_conj_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:36:20.956993+00:00
-- url     : https://prove2.me/theorems/a0630ed0-e880-45c2-bfd6-5b4edcdd82eb
-- title:
--   Tanner Lifted Product: lps Quaternion Div mul conj mul eq
-- statement:
--   If `t * β̄` is coordinatewise divisible by `p` and `β` has norm `p`,
--   the exact quotient is a genuine right factorization of `t`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L99-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L99-L110

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsQuaternionDiv_mul_conj_mul_eq
    (hp : p.Prime) {t beta : LPSQuaternion}
    (hbeta : beta.norm = p)
    (hdiv : (t * beta.conj).CoordinatesDvd (p : ℤ)) :
    lpsQuaternionDiv (p : ℤ) (t * beta.conj) * beta = t := by sorry
