-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:35:40.765487+00:00
-- url     : https://prove2.me/theorems/4e842b0f-18ae-4e34-898b-c4748a01022e
-- title:
--   Tanner Lifted Product: coeff lps Trace Theta Series prime pow eq two mul alternating Closed Count of surjective
-- statement:
--   Theta-coefficient form of the same exact conditional identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L479-L488
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L479-L488

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_alternatingClosedCount_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) =
      2 * lpsAlternatingClosedReducedWordCount a n := by sorry
