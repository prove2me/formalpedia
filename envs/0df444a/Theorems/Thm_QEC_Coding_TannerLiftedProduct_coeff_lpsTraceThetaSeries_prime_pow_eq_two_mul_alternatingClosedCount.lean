-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:01:13.6232+00:00
-- url     : https://prove2.me/theorems/ee58a736-8005-4832-b87c-03719cda6bfa
-- title:
--   Tanner Lifted Product: coeff lps Trace Theta Series prime pow eq two mul alternating Closed Count
-- statement:
--   Coefficient form of the exact LPS trace-count identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L311-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionFactorization.lean#L311-L316

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount
    (a : LPSResiduePrime p) (n : ℕ) :
    PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) =
      2 * lpsAlternatingClosedReducedWordCount a n := by sorry
