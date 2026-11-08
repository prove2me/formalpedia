-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_lpsQuaternionDiv_mul_conj
-- name    : QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionDiv_mul_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:36:20.602247+00:00
-- url     : https://prove2.me/theorems/f1f8f625-2796-4d1a-a2cb-73d1eb73d90c
-- title:
--   Tanner Lifted Product: norm lps Quaternion Div mul conj
-- statement:
--   The quotient in the preceding right factorization has norm one lower
--   power of `p`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L114-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionExactDivision.lean#L114-L131

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionDiv_mul_conj
    (hp : p.Prime) {n : ℕ} {t beta : LPSQuaternion}
    (ht : t.norm = (p : ℤ) ^ (n + 1))
    (hbeta : beta.norm = p)
    (hdiv : (t * beta.conj).CoordinatesDvd (p : ℤ)) :
    (lpsQuaternionDiv (p : ℤ) (t * beta.conj)).norm =
      (p : ℤ) ^ n := by sorry
