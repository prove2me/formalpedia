-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:23:19.561858+00:00
-- url     : https://prove2.me/theorems/d773fc16-4a7f-42bb-9f6c-5f7eb16ed272
-- title:
--   Tanner Lifted Product: lps Reduced Word Element one
-- statement:
--   The Tanner Lifted Product construction uses the lps Reduced Word Element one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L715-L733
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L715-L733

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_one
    (a : LPSResiduePrime p) :
    lpsReducedWordElement a 1 =
      cayleyGeneratorSum (lpsQuaternionLabel a) := by sorry
