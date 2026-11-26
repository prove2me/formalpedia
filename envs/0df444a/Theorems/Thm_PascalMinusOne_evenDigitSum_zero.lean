-- Prove2me | Theorems.Thm_PascalMinusOne_evenDigitSum_zero
-- name    : PascalMinusOne.evenDigitSum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:08.404939+00:00
-- url     : https://prove2.me/theorems/223f0dce-b458-5d67-ad8f-d16ea9c9bcd7
-- title:
--   Pascal Minus One: even Digit Sum zero
-- statement:
--   The Pascal Minus One construction uses the even Digit Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L34-L35
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/Digits.lean#L34-L35

import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_PascalMinusOne_Digits
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.evenDigitSum_zero (p : ℕ) : evenDigitSum p 0 = 0 := by sorry
