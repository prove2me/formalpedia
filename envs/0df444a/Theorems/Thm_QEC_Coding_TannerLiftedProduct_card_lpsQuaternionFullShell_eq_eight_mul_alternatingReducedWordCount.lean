-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:29:08.627285+00:00
-- url     : https://prove2.me/theorems/8b4d8d24-97b3-4c50-8329-2b0ad53f0992
-- title:
--   Tanner Lifted Product: card lps Quaternion Full Shell eq eight mul alternating Reduced Word Count
-- statement:
--   The full norm-`p^n` quaternion shell has exactly eight times as many
--   elements as the alternating reduced spheres.  This is the finite cardinality
--   identity used to turn existence of the LPS normal form into uniqueness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L89-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimePowerCount.lean#L89-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsQuaternionFullShell_eq_eight_mul_alternatingReducedWordCount
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsQuaternionFullShell (p ^ n)).card =
      8 * lpsAlternatingReducedWordCount hp.pos n := by sorry
