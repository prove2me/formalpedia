-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_lpsReducedWord_tail_add_two
-- name    : QEC.Coding.TannerLiftedProduct.sum_lpsReducedWord_tail_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:31.139684+00:00
-- url     : https://prove2.me/theorems/451327ad-8559-49b8-98f3-030cc9b6a453
-- title:
--   Tanner Lifted Product: sum lps Reduced Word tail add two
-- statement:
--   Summing the products left after one immediate backtrack gives exactly
--   `p` copies of the preceding reduced sphere.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L384-L451
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L384-L451

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.sum_lpsReducedWord_tail_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    (∑ word : LPSReducedWord a.degreePrime.pos (n + 2),
      MonoidAlgebra.single
        (cayleyVectorWordProduct (lpsQuaternionLabel a) word.1.tail) (1 : ℂ)) =
      p • lpsReducedWordElement a (n + 1) := by sorry
