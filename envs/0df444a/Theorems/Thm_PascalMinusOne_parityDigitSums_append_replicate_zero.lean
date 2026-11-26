-- Prove2me | Theorems.Thm_PascalMinusOne_parityDigitSums_append_replicate_zero
-- name    : PascalMinusOne.parityDigitSums_append_replicate_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:13.627687+00:00
-- url     : https://prove2.me/theorems/bb0c294b-d3ae-5771-90ff-17d2660128bf
-- title:
--   Pascal Minus One: parity Digit Sums append replicate zero
-- statement:
--   A suffix of zero digits does not change the even/odd digit totals.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L92-L102
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L92-L102

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.parityDigitSums_append_replicate_zero (L : List ℕ) (n : ℕ) :
    parityDigitSums (L ++ List.replicate n 0) = parityDigitSums L := by sorry
