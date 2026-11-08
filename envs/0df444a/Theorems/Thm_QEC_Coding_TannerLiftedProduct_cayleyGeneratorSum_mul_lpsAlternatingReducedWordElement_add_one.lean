-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyGeneratorSum_mul_lpsAlternatingReducedWordElement_add_one
-- name    : QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_mul_lpsAlternatingReducedWordElement_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:27:09.236201+00:00
-- url     : https://prove2.me/theorems/ff264f4b-d07b-4304-b3dc-7e8ad6af8640
-- title:
--   Tanner Lifted Product: cayley Generator Sum mul lps Alternating Reduced Word Element add one
-- statement:
--   The alternating reduced spheres satisfy the exact LPS Hecke recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L823-L848
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L823-L848

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_mul_lpsAlternatingReducedWordElement_add_one
    (a : LPSResiduePrime p) (n : ℕ) :
    cayleyGeneratorSum (lpsQuaternionLabel a) *
        lpsAlternatingReducedWordElement a (n + 1) =
      lpsAlternatingReducedWordElement a (n + 2) +
        p • lpsAlternatingReducedWordElement a n := by sorry
