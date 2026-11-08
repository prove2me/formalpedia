-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsAlternatingReducedWordElement_one
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsAlternatingReducedWordElement_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:26:54.15917+00:00
-- url     : https://prove2.me/theorems/f57fc9cc-6cff-4d62-9b6a-98988d49183d
-- title:
--   Tanner Lifted Product: coeff lps Alternating Reduced Word Element one
-- statement:
--   The identity coefficient of the alternating reduced-sphere element is the
--   LPS closed-walk count `L_n(e,e)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L678-L696
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L678-L696

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsAlternatingReducedWordElement_one
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsAlternatingReducedWordElement a n).coeff 1 =
      (lpsAlternatingClosedReducedWordCount a n : ℂ) := by sorry
