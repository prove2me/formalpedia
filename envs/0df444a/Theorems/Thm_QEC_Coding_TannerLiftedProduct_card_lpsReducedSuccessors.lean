-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedSuccessors
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsReducedSuccessors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:40.220108+00:00
-- url     : https://prove2.me/theorems/011f9aa6-a008-4097-a4be-134d0b35b229
-- title:
--   Tanner Lifted Product: card lps Reduced Successors
-- statement:
--   Exactly `p` directions remain after forbidding immediate backtracking.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L65-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L65-L72

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsReducedSuccessors
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSGeneratorIndex p) :
    (lpsReducedSuccessors hp.pos t).card = p := by sorry
