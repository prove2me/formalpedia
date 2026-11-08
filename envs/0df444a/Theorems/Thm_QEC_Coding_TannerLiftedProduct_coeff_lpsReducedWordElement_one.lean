-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsReducedWordElement_one
-- name    : QEC.Coding.TannerLiftedProduct.coeff_lpsReducedWordElement_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:26:48.975101+00:00
-- url     : https://prove2.me/theorems/de4fa434-4621-4eef-82de-e3d19f21759d
-- title:
--   Tanner Lifted Product: coeff lps Reduced Word Element one
-- statement:
--   The identity coefficient of a reduced-word sphere is its number of closed
--   reduced words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L650-L655
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L650-L655

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.coeff_lpsReducedWordElement_one
    (a : LPSResiduePrime p) (n : ℕ) :
    (lpsReducedWordElement a n).coeff 1 =
      ((lpsClosedReducedWords a n).card : ℂ) := by sorry
