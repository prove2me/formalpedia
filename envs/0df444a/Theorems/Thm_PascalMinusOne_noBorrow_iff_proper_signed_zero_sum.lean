-- Prove2me | Theorems.Thm_PascalMinusOne_noBorrow_iff_proper_signed_zero_sum
-- name    : PascalMinusOne.noBorrow_iff_proper_signed_zero_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:41.133304+00:00
-- url     : https://prove2.me/theorems/96fae698-90da-4b2f-abf7-b721828cdee5
-- title:
--   Pascal Minus One: no Borrow iff proper signed zero sum
-- statement:
--   No-borrow admissible indices are exactly proper zero-sum signed submultisets.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L299-L419
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L299-L419

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.noBorrow_iff_proper_signed_zero_sum
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1) (hmN : m ∣ N) :
    (∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 0) ↔
      HasProperZeroSubmultiset m (evenDigitSum p N) (oddDigitSum p N) := by sorry
