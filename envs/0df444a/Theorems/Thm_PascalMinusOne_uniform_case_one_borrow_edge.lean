-- Prove2me | Theorems.Thm_PascalMinusOne_uniform_case_one_borrow_edge
-- name    : PascalMinusOne.uniform_case_one_borrow_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:38.680291+00:00
-- url     : https://prove2.me/theorems/fb3b2327-d387-5fc3-8199-ff5040924a46
-- title:
--   Pascal Minus One: uniform case one borrow edge
-- statement:
--   In the edge case `p = m-1`, the repaired witness uses the leading occupied
--   digit `t` and a lower occupied digit `s` of the same parity:
--   `k = p^(t-1) + p^s`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L607-L898
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L607-L898

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.uniform_case_one_borrow_edge
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p = m - 1)
    (hmN : m ∣ N) (hNm : m < N)
    (huniform :
      (evenDigitSum p N = m ∧ oddDigitSum p N = 0) ∨
      (evenDigitSum p N = 0 ∧ oddDigitSum p N = m)) :
    ∃ t s k,
      s < t ∧ Occupied p N t ∧ Occupied p N s ∧
      k = p ^ (t - 1) + p ^ s ∧
      Admissible N m k ∧ padicValNat p (N.choose k) = 1 := by sorry
