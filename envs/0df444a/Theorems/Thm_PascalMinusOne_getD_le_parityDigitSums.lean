-- Prove2me | Theorems.Thm_PascalMinusOne_getD_le_parityDigitSums
-- name    : PascalMinusOne.getD_le_parityDigitSums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:33.311569+00:00
-- url     : https://prove2.me/theorems/b4e43ea7-d816-5f76-be7a-103f2b2a4fcc
-- title:
--   Pascal Minus One: get D le parity Digit Sums
-- statement:
--   A digit is bounded by the parity total containing its position.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L422-L438
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L422-L438

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.getD_le_parityDigitSums (L : List ℕ) (i : ℕ) :
    L.getD i 0 ≤
      if Even i then (parityDigitSums L).1 else (parityDigitSums L).2 := by sorry
