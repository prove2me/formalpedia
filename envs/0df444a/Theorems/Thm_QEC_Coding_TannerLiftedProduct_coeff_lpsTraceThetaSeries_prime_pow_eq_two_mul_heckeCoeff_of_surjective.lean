-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:36:49.699322+00:00
-- url     : https://prove2.me/theorems/3eafd491-8e1f-4bc4-b22e-cc34eacedf4f
-- title:
--   Tanner Lifted Product: coeff lps Trace Theta Series prime pow eq two mul hecke Coeff of surjective
-- statement:
--   Complex-coefficient Hecke form of the exact conditional LPS identity:
--   the theta coefficient at `p^n` is twice the identity coefficient of the
--   finite Hecke element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L493-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean#L493-L502

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries_prime_pow_eq_two_mul_heckeCoeff_of_surjective
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    ((PowerSeries.coeff (p ^ n) (lpsTraceThetaSeries a.q) : ℕ) : ℂ) =
      2 * (lpsFiniteHeckeElement a n).coeff 1 := by sorry
