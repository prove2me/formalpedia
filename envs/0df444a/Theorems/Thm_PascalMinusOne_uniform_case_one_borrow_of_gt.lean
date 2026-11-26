-- Prove2me | Theorems.Thm_PascalMinusOne_uniform_case_one_borrow_of_gt
-- name    : PascalMinusOne.uniform_case_one_borrow_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:36.198365+00:00
-- url     : https://prove2.me/theorems/e3fd7c7f-104d-5db8-939b-2417f0b65d67
-- title:
--   Pascal Minus One: uniform case one borrow of gt
-- statement:
--   In a uniform token case with `p > m`, placing the digit `m` immediately below
--   the leading occupied digit forces exactly one borrow.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L450-L602
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L450-L602

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.uniform_case_one_borrow_of_gt
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hpmgt : m < p) (hmN : m ∣ N) (hNm : m < N)
    (huniform :
      (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
      (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) :
    ∃ k, Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by sorry
