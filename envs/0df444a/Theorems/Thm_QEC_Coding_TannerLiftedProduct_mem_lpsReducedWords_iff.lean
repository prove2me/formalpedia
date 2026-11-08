-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_lpsReducedWords_iff
-- name    : QEC.Coding.TannerLiftedProduct.mem_lpsReducedWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:26:18.147325+00:00
-- url     : https://prove2.me/theorems/6385a29b-6ff3-4d35-bfe4-c3fb7c9507e5
-- title:
--   Tanner Lifted Product: mem lps Reduced Words iff
-- statement:
--   The Tanner Lifted Product construction uses the mem lps Reduced Words iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L129-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L129-L134

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.mem_lpsReducedWords_iff
    (hp : 0 < p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n) :
    word ∈ lpsReducedWords hp n ↔
      LPSWordIsReduced hp word.1 := by sorry
