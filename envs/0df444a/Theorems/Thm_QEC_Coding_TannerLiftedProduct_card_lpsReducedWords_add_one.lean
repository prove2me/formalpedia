-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_add_one
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:48.107818+00:00
-- url     : https://prove2.me/theorems/eb015d33-5c69-42b2-badd-449d21a93b59
-- title:
--   Tanner Lifted Product: card lps Reduced Words add one
-- statement:
--   Exact size of the radius-`n+1` sphere in the free `(p+1)`-regular LPS
--   quaternion tree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L307-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L307-L316

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_add_one
    (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    (lpsReducedWords hp.pos (n + 1)).card =
      (p + 1) * p ^ n := by sorry
