-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyGeneratorSum_mul_lpsReducedWordElement_add_two
-- name    : QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_mul_lpsReducedWordElement_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:04.456212+00:00
-- url     : https://prove2.me/theorems/086dee3d-8081-4e5f-b3ee-e31f3317ed43
-- title:
--   Tanner Lifted Product: cayley Generator Sum mul lps Reduced Word Element add two
-- statement:
--   Exact non-backtracking recurrence in the finite LPS group algebra.  The
--   coefficient `p` is proved by the reduced-prefix fibre count above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L595-L616
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L595-L616

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_mul_lpsReducedWordElement_add_two
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyGeneratorSum (lpsQuaternionLabel a) *
        lpsReducedWordElement a (n + 2) =
      lpsReducedWordElement a (n + 3) +
        p • lpsReducedWordElement a (n + 1) := by sorry
