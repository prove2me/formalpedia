-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyVectorWordProduct_lps_backtrack
-- name    : QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lps_backtrack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:43.12211+00:00
-- url     : https://prove2.me/theorems/ca70bdb5-0ca5-463a-8792-bc449ec5bac2
-- title:
--   Tanner Lifted Product: cayley Vector Word Product lps backtrack
-- statement:
--   Prefixing a letter and then its conjugate cancels in the finite LPS
--   vertex group.  This is the algebraic half of the non-backtracking Hecke
--   recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L356-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L356-L362

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lps_backtrack
    (a : LPSResiduePrime p) (t : LPSGeneratorIndex p) {n : ℕ}
    (tail : List.Vector (LPSGeneratorIndex p) n) :
    cayleyVectorWordProduct (lpsQuaternionLabel a)
        (t ::ᵥ (lpsGeneratorConjEquiv a.degreePrime.pos t ::ᵥ tail)) =
      cayleyVectorWordProduct (lpsQuaternionLabel a) tail := by sorry
