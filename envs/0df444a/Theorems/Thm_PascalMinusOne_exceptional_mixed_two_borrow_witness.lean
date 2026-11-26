-- Prove2me | Theorems.Thm_PascalMinusOne_exceptional_mixed_two_borrow_witness
-- name    : PascalMinusOne.exceptional_mixed_two_borrow_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:56.048494+00:00
-- url     : https://prove2.me/theorems/2a84182e-593d-48f0-9283-3709450d6f5e
-- title:
--   Pascal Minus One: exceptional mixed two borrow witness
-- statement:
--   In the exceptional mixed case, the witness
--   `p^(t-1) + p^(t-2)` creates exactly the two carries at boundaries `t-1` and `t`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1613-L1786
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1613-L1786

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.exceptional_mixed_two_borrow_witness
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 2 := by sorry
