-- Prove2me | Theorems.Thm_PascalMinusOne_parityDigitSums_digits_ofDigits
-- name    : PascalMinusOne.parityDigitSums_digits_ofDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:41.396315+00:00
-- url     : https://prove2.me/theorems/19903be0-3472-403f-a9e3-78873685dbe1
-- title:
--   Pascal Minus One: parity Digit Sums digits of Digits
-- statement:
--   Removing any high zero digits from a valid base-`p` representation does not change its
--   parity digit totals.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L286-L296
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L286-L296

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.parityDigitSums_digits_ofDigits {p : ℕ} (hp : 2 ≤ p) {L : List ℕ}
    (hL : ∀ d ∈ L, d < p) :
    parityDigitSums (Nat.digits p (Nat.ofDigits p L)) = parityDigitSums L := by sorry
