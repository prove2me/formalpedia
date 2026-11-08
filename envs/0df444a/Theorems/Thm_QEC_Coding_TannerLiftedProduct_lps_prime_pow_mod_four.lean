-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lps_prime_pow_mod_four
-- name    : QEC.Coding.TannerLiftedProduct.lps_prime_pow_mod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:53.01584+00:00
-- url     : https://prove2.me/theorems/187cefb4-bc25-482d-93b2-8f935cc222b4
-- title:
--   Tanner Lifted Product: lps prime pow mod four
-- statement:
--   Powers of an integer congruent to one modulo four stay congruent to one
--   modulo four.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L20-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L20-L25

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lps_prime_pow_mod_four
    (hp4 : p % 4 = 1) (k : ℕ) : p ^ k % 4 = 1 := by sorry
