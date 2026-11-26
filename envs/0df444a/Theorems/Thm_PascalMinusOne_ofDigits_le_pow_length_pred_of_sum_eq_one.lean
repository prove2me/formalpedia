-- Prove2me | Theorems.Thm_PascalMinusOne_ofDigits_le_pow_length_pred_of_sum_eq_one
-- name    : PascalMinusOne.ofDigits_le_pow_length_pred_of_sum_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:41.208355+00:00
-- url     : https://prove2.me/theorems/854d22e5-afce-5625-8ede-476dc2e710e4
-- title:
--   Pascal Minus One: of Digits le pow length pred of sum eq one
-- statement:
--   A little-endian natural digit list with total digit mass one is bounded by
--   its highest available place value.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L917-L953
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L917-L953

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.ofDigits_le_pow_length_pred_of_sum_eq_one {p : ℕ} (hp : 0 < p) :
    ∀ L : List ℕ, L.sum = 1 →
      Nat.ofDigits p L ≤ p ^ (L.length - 1) := by sorry
