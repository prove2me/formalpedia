-- Prove2me | Theorems.Thm_PascalMinusOne_digitAt_le_parityDigitSum
-- name    : PascalMinusOne.digitAt_le_parityDigitSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:46.853068+00:00
-- url     : https://prove2.me/theorems/3bd7aa42-3358-517e-815b-02eeb69eaa22
-- title:
--   Pascal Minus One: digit At le parity Digit Sum
-- statement:
--   The arithmetic digit accessor is bounded by the corresponding parity digit sum.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L441-L446
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L441-L446

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.digitAt_le_parityDigitSum {p N i : ℕ} (hp : 2 ≤ p) :
    digitAt p N i ≤
      if Even i then evenDigitSum p N else oddDigitSum p N := by sorry
