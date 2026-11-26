-- Prove2me | Theorems.Thm_PascalMinusOne_parityDigitSums_cons
-- name    : PascalMinusOne.parityDigitSums_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:09.939541+00:00
-- url     : https://prove2.me/theorems/f69320a7-26a8-43fc-aef2-1fd9b7ccc41f
-- title:
--   Pascal Minus One: parity Digit Sums cons
-- statement:
--   The Pascal Minus One construction uses the parity Digit Sums cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L30-L32
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L30-L32

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.parityDigitSums_cons (d : ℕ) (ds : List ℕ) :
    parityDigitSums (d :: ds) =
      (d + (parityDigitSums ds).2, (parityDigitSums ds).1) := by sorry

attribute [defeq] PascalMinusOne.parityDigitSums_cons
