-- Prove2me | Theorems.Thm_PascalMinusOne_exceptional_mixed_no_one_borrow
-- name    : PascalMinusOne.exceptional_mixed_no_one_borrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:54.993606+00:00
-- url     : https://prove2.me/theorems/a859ffd2-65f4-5ec0-8d45-0efe4b069539
-- title:
--   Pascal Minus One: exceptional mixed no one borrow
-- statement:
--   In the exceptional mixed case, an admissible index cannot create exactly one carry.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1281-L1609
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1281-L1609

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.exceptional_mixed_no_one_borrow
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∀ k, Admissible N m k → padicValNat p (N.choose k) ≠ 1 := by sorry
