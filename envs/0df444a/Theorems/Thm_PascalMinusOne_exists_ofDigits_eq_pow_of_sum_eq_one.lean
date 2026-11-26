-- Prove2me | Theorems.Thm_PascalMinusOne_exists_ofDigits_eq_pow_of_sum_eq_one
-- name    : PascalMinusOne.exists_ofDigits_eq_pow_of_sum_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:54.93581+00:00
-- url     : https://prove2.me/theorems/b09d1a6b-fff4-411d-8c08-66dc833cb1c5
-- title:
--   Pascal Minus One: exists of Digits eq pow of sum eq one
-- statement:
--   A natural digit list of total mass one represents a single power of the base.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1100-L1127
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1100-L1127

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.exists_ofDigits_eq_pow_of_sum_eq_one (p : ℕ) :
    ∀ L : List ℕ, L.sum = 1 →
      ∃ i, i < L.length ∧ Nat.ofDigits p L = p ^ i := by sorry
