-- Prove2me | Theorems.Thm_PascalMinusOne_ofDigits_neg_one_eq_parityDigitSums
-- name    : PascalMinusOne.ofDigits_neg_one_eq_parityDigitSums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:16.179296+00:00
-- url     : https://prove2.me/theorems/8694be88-d443-4572-a590-2201ee3b7fbb
-- title:
--   Pascal Minus One: of Digits neg one eq parity Digit Sums
-- statement:
--   Evaluating a little-endian digit list at base `-1` gives its even-position sum minus
--   its odd-position sum.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L55-L62
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L55-L62

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.ofDigits_neg_one_eq_parityDigitSums (L : List ℕ) :
    Nat.ofDigits (-1 : ℤ) L =
      ((parityDigitSums L).1 : ℤ) - ((parityDigitSums L).2 : ℤ) := by sorry
