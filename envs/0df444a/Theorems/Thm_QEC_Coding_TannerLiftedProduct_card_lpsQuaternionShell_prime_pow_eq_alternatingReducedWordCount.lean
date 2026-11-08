-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:28:31.142192+00:00
-- url     : https://prove2.me/theorems/f8c181c1-08c7-4e4b-9f32-b5fc00388d06
-- title:
--   Tanner Lifted Product: card lps Quaternion Shell prime pow eq alternating Reduced Word Count
-- statement:
--   The normalized positive-first-coordinate shell at norm `p^n` has the
--   same size as the alternating reduced spheres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L98-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L98-L108

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionShell_prime_pow_eq_alternatingReducedWordCount
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsQuaternionShell (p ^ n)).card =
      lpsAlternatingReducedWordCount hp.pos n := by sorry
