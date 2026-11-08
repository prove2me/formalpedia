-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_zero
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:21:58.844872+00:00
-- url     : https://prove2.me/theorems/6744096e-3336-49a2-951e-9e9963658d65
-- title:
--   Tanner Lifted Product: card lps Reduced Words zero
-- statement:
--   The Tanner Lifted Product construction uses the card lps Reduced Words zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L276-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L276-L287

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_zero (hp : 0 < p) :
    (lpsReducedWords hp 0).card = 1 := by sorry
