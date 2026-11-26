-- Prove2me | Theorems.Thm_PascalMinusOne_parityDigitSums_nil
-- name    : PascalMinusOne.parityDigitSums_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:07.30365+00:00
-- url     : https://prove2.me/theorems/d7c2da6e-da38-5d74-80dd-38f45b0c9ae2
-- title:
--   Pascal Minus One: parity Digit Sums nil
-- statement:
--   The Pascal Minus One construction uses the parity Digit Sums nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L28-L28
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L28-L28

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.parityDigitSums_nil : parityDigitSums [] = (0, 0) := by sorry

attribute [defeq] PascalMinusOne.parityDigitSums_nil
