-- Prove2me | Theorems.Thm_PascalMinusOne_parityDigitSums_add_eq_sum
-- name    : PascalMinusOne.parityDigitSums_add_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:47.356002+00:00
-- url     : https://prove2.me/theorems/0a169290-3c96-4850-980d-b5e2ea87fa9d
-- title:
--   Pascal Minus One: parity Digit Sums add eq sum
-- statement:
--   The two parity digit totals add to the ordinary digit sum.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L84-L89
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L84-L89

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.parityDigitSums_add_eq_sum (L : List ℕ) :
    (parityDigitSums L).1 + (parityDigitSums L).2 = L.sum := by sorry
