-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyGeneratorSum_mul_lpsReducedWordElement_one
-- name    : QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_mul_lpsReducedWordElement_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:27:00.571617+00:00
-- url     : https://prove2.me/theorems/3a65e393-edbd-44f3-82f9-6dbebd2c285b
-- title:
--   Tanner Lifted Product: cayley Generator Sum mul lps Reduced Word Element one
-- statement:
--   Exceptional first non-backtracking recurrence at the root of the
--   `(p+1)`-regular tree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L788-L809
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L788-L809

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.cayleyGeneratorSum_mul_lpsReducedWordElement_one
    (a : LPSResiduePrime p) :
    cayleyGeneratorSum (lpsQuaternionLabel a) *
        lpsReducedWordElement a 1 =
      lpsReducedWordElement a 2 +
        (p + 1) • lpsReducedWordElement a 0 := by sorry
