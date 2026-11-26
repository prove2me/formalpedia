-- Prove2me | Theorems.Thm_PascalMinusOne_parityDigitSums_mono
-- name    : PascalMinusOne.parityDigitSums_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:17.219349+00:00
-- url     : https://prove2.me/theorems/8113e892-12d5-5b87-912b-728056034d29
-- title:
--   Pascal Minus One: parity Digit Sums mono
-- statement:
--   Componentwise-bounded digit lists have componentwise-bounded parity totals.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L110-L118
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L110-L118

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.parityDigitSums_mono {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) :
    (parityDigitSums S).1 ≤ (parityDigitSums D).1 ∧
      (parityDigitSums S).2 ≤ (parityDigitSums D).2 := by sorry
