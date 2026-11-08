-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_one
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:23:06.840814+00:00
-- url     : https://prove2.me/theorems/066a781d-fdf6-42e0-817c-700bde7bc130
-- title:
--   Tanner Lifted Product: card lps Reduced Words one
-- statement:
--   The Tanner Lifted Product construction uses the card lps Reduced Words one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L289-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L289-L303

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_one
    (hp : p.Prime) (hp4 : p % 4 = 1) :
    (lpsReducedWords hp.pos 1).card = p + 1 := by sorry
