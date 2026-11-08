-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coordinatesDvd_wordProduct_mul_conj_of_mem_getLast
-- name    : QEC.Coding.TannerLiftedProduct.coordinatesDvd_wordProduct_mul_conj_of_mem_getLast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:52:47.63292+00:00
-- url     : https://prove2.me/theorems/5ef8df99-8228-48db-a1f7-cd39ea1d119e
-- title:
--   Tanner Lifted Product: coordinates Dvd word Product mul conj of mem get Last
-- statement:
--   If `x` is the last letter of a word, multiplying its quaternion product
--   by `x̄` creates a central factor of `p`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L64-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L64-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coordinatesDvd_wordProduct_mul_conj_of_mem_getLast
    (hp : p.Prime) (word : List (LPSGeneratorIndex p))
    (x : LPSGeneratorIndex p) (hx : x ∈ word.getLast?) :
    (lpsQuaternionWordProduct word * x.1.conj).CoordinatesDvd (p : ℤ) := by sorry
