-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_lpsClosedReducedWords_iff
-- name    : QEC.Coding.TannerLiftedProduct.mem_lpsClosedReducedWords_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:26:46.363774+00:00
-- url     : https://prove2.me/theorems/ecedbbf1-005f-4d03-9091-bbb66434a99c
-- title:
--   Tanner Lifted Product: mem lps Closed Reduced Words iff
-- statement:
--   The Tanner Lifted Product construction uses the mem lps Closed Reduced Words iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L640-L646
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L640-L646

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.mem_lpsClosedReducedWords_iff
    (a : LPSResiduePrime p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n) :
    word ∈ lpsClosedReducedWords a n ↔
      LPSWordIsReduced a.degreePrime.pos word.1 ∧
        cayleyVectorWordProduct (lpsQuaternionLabel a) word = 1 := by sorry
