-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_add_two
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:23.881331+00:00
-- url     : https://prove2.me/theorems/1638f53f-bbc2-42d3-a5b5-b3db8ae50d05
-- title:
--   Tanner Lifted Product: card lps Reduced Words add two
-- statement:
--   Finset form of the exact `p`-branching recurrence for reduced words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L268-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L268-L274

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_add_two
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsReducedWords hp.pos (n + 2)).card =
      p * (lpsReducedWords hp.pos (n + 1)).card := by sorry
