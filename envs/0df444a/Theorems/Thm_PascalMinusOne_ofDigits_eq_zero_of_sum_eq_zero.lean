-- Prove2me | Theorems.Thm_PascalMinusOne_ofDigits_eq_zero_of_sum_eq_zero
-- name    : PascalMinusOne.ofDigits_eq_zero_of_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:35.666733+00:00
-- url     : https://prove2.me/theorems/c525415d-9e61-5dcb-83dc-61ae28f42bb6
-- title:
--   Pascal Minus One: of Digits eq zero of sum eq zero
-- statement:
--   A natural digit list with zero total digit mass evaluates to zero in every base.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L901-L913
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L901-L913

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.ofDigits_eq_zero_of_sum_eq_zero (p : ℕ) :
    ∀ L : List ℕ, L.sum = 0 → Nat.ofDigits p L = 0 := by sorry
