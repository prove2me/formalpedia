-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordElement_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:22:51.328528+00:00
-- url     : https://prove2.me/theorems/205d175d-4020-43a8-996c-915c7d6242bf
-- title:
--   Tanner Lifted Product: lps Alternating Reduced Word Element one
-- statement:
--   The Tanner Lifted Product construction uses the lps Alternating Reduced Word Element one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L816-L820
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L816-L820

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_one
    (a : LPSResiduePrime p) :
    lpsAlternatingReducedWordElement a 1 =
      cayleyGeneratorSum (lpsQuaternionLabel a) := by sorry
