-- Prove2me | Theorems.Thm_PascalMinusOne_parityDigitSums_digitsAppend
-- name    : PascalMinusOne.parityDigitSums_digitsAppend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:18.536545+00:00
-- url     : https://prove2.me/theorems/c3520e8a-ec3a-5007-9027-921c81abf3f9
-- title:
--   Pascal Minus One: parity Digit Sums digits Append
-- statement:
--   Padding a base-`p` digit list to a fixed length leaves its parity totals unchanged.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L105-L107
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L105-L107

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.parityDigitSums_digitsAppend (p l n : ℕ) :
    parityDigitSums (Nat.digitsAppend p l n) = parityDigitSums (Nat.digits p n) := by sorry
