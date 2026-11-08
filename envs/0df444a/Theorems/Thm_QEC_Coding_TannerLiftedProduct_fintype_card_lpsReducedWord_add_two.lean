-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_fintype_card_lpsReducedWord_add_two
-- name    : QEC.Coding.TannerLiftedProduct.fintype_card_lpsReducedWord_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:26:03.228568+00:00
-- url     : https://prove2.me/theorems/fa5cb9a1-c0a4-44c1-8295-af9775a4fa62
-- title:
--   Tanner Lifted Product: fintype card lps Reduced Word add two
-- statement:
--   After the first letter, every reduced LPS word has exactly `p` possible
--   new prefixes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L251-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L251-L265

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.fintype_card_lpsReducedWord_add_two
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    Fintype.card (LPSReducedWord hp.pos (n + 2)) =
      p * Fintype.card (LPSReducedWord hp.pos (n + 1)) := by sorry
