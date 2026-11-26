-- Prove2me | Theorems.Thm_PascalMinusOne_mixed_eq_sum_two_powers
-- name    : PascalMinusOne.mixed_eq_sum_two_powers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:45.846868+00:00
-- url     : https://prove2.me/theorems/0afa5ee2-5dc8-4e94-b7ba-6fa47c7b868a
-- title:
--   Pascal Minus One: mixed eq sum two powers
-- statement:
--   In the mixed case the base-`p` expansion is exactly two unit powers, and
--   their exponents have opposite parity.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1184-L1278
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1184-L1278

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.mixed_eq_sum_two_powers
    {m p N : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hpm : p % m = m - 1)
    (hmN : m ∣ N)
    (hmixed : evenDigitSum p N = 1 ∧ oddDigitSum p N = 1) :
    ∃ s t, s < t ∧ N = p ^ s + p ^ t ∧ ¬ (Even s ↔ Even t) := by sorry
