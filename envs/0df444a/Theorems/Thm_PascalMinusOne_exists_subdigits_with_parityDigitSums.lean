-- Prove2me | Theorems.Thm_PascalMinusOne_exists_subdigits_with_parityDigitSums
-- name    : PascalMinusOne.exists_subdigits_with_parityDigitSums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:20.181716+00:00
-- url     : https://prove2.me/theorems/40ad6d71-c3e8-5e3e-94f3-b91c5dafb4a2
-- title:
--   Pascal Minus One: exists subdigits with parity Digit Sums
-- statement:
--   Any prescribed pair of parity totals below those of a digit list can be realised by
--   a componentwise-bounded digit list of the same length.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L122-L148
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L122-L148

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.exists_subdigits_with_parityDigitSums
    (D : List ℕ) {a b : ℕ}
    (ha : a ≤ (parityDigitSums D).1)
    (hb : b ≤ (parityDigitSums D).2) :
    ∃ S : List ℕ,
      List.Forall₂ (· ≤ ·) S D ∧ parityDigitSums S = (a, b) := by sorry
