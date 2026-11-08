-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_prime_pow
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:27:11.382001+00:00
-- url     : https://prove2.me/theorems/7ab08211-551a-4e49-8182-be8dfec33bbb
-- title:
--   Tanner Lifted Product: coeff jacobi Four Square Series prime pow
-- statement:
--   Jacobi's divisor sum at `p^k` is the geometric sum
--   `8 (1 + p + ... + p^k)` when `p = 1 mod 4`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L36-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L36-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_prime_pow
    (hp : p.Prime) (hp4 : p % 4 = 1) (k : ℕ) :
    PowerSeries.coeff (p ^ k) jacobiFourSquareSeries =
      8 * ∑ i ∈ Finset.range (k + 1), p ^ i := by sorry
