-- Prove2me | Theorems.Thm_PascalMinusOne_oddDigitSum_zero
-- name    : PascalMinusOne.oddDigitSum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:10.735799+00:00
-- url     : https://prove2.me/theorems/60ec14f5-c911-42f5-8431-be805fb0b1c5
-- title:
--   Pascal Minus One: odd Digit Sum zero
-- statement:
--   The Pascal Minus One construction uses the odd Digit Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L37-L38
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L37-L38

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.oddDigitSum_zero (p : ℕ) : oddDigitSum p 0 = 0 := by sorry
