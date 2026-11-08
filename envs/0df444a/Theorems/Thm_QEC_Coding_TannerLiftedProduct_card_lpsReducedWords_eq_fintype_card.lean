-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_eq_fintype_card
-- name    : QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_eq_fintype_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:25:03.266252+00:00
-- url     : https://prove2.me/theorems/6bceebcf-c44a-4cb1-b2d1-e0ce30bafaf8
-- title:
--   Tanner Lifted Product: card lps Reduced Words eq fintype card
-- statement:
--   The subtype and finite-set presentations of reduced words have the same
--   cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L241-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean#L241-L247

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_eq_fintype_card
    (hp : 0 < p) (n : ℕ) :
    (lpsReducedWords hp n).card =
      Fintype.card (LPSReducedWord hp n) := by sorry
