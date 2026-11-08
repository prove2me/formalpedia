-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGeneratorConjEquiv_ne
-- name    : QEC.Coding.TannerLiftedProduct.lpsGeneratorConjEquiv_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:30:00.950269+00:00
-- url     : https://prove2.me/theorems/94b39533-1723-40f8-9893-fb49ec5033fe
-- title:
--   Tanner Lifted Product: lps Generator Conj Equiv ne
-- statement:
--   A normalized prime-norm LPS generator is never its own conjugate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L27-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L27-L50

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsGeneratorConjEquiv_ne
    (hp : p.Prime) (t : LPSGeneratorIndex p) :
    lpsGeneratorConjEquiv hp.pos t ≠ t := by sorry
