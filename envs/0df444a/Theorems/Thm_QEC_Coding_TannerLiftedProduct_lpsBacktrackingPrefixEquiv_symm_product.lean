-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsBacktrackingPrefixEquiv_symm_product
-- name    : QEC.Coding.TannerLiftedProduct.lpsBacktrackingPrefixEquiv_symm_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:23:11.776543+00:00
-- url     : https://prove2.me/theorems/58f7fc98-9b4a-47d2-90e9-f35025739c77
-- title:
--   Tanner Lifted Product: lps Backtracking Prefix Equiv symm product
-- statement:
--   Product carried by the canonical forbidden prefix reduces to the tail of
--   the reduced word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L366-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L366-L380

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsBacktrackingPrefixEquiv_symm_product
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSReducedWord a.degreePrime.pos (n + 1)) :
    lpsQuaternionLabel a
        ((lpsBacktrackingPrefixEquiv a.degreePrime n).symm word).1.1 *
      cayleyVectorWordProduct (lpsQuaternionLabel a)
        ((lpsBacktrackingPrefixEquiv a.degreePrime n).symm word).1.2.1 =
      cayleyVectorWordProduct (lpsQuaternionLabel a) word.1.tail := by sorry
