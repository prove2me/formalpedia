-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordElement_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:23:32.868198+00:00
-- url     : https://prove2.me/theorems/2b0c84a2-de48-457f-9c12-6be8bb331361
-- title:
--   Tanner Lifted Product: lps Alternating Reduced Word Element zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Alternating Reduced Word Element zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L811-L814
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L811-L814

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_zero
    (a : LPSResiduePrime p) :
    lpsAlternatingReducedWordElement a 0 = 1 := by sorry
