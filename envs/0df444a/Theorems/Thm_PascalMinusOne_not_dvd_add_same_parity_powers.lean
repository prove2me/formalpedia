-- Prove2me | Theorems.Thm_PascalMinusOne_not_dvd_add_same_parity_powers
-- name    : PascalMinusOne.not_dvd_add_same_parity_powers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:38.123745+00:00
-- url     : https://prove2.me/theorems/ff94c243-aae3-5d53-9dac-40b6a07bd850
-- title:
--   Pascal Minus One: not dvd add same parity powers
-- statement:
--   Two nonzero coefficient blocks on same-parity powers cannot form a multiple of `m`
--   when their coefficient sum is strictly below `m` and `p ≡ -1 (mod m)`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1131-L1180
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L1131-L1180

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.not_dvd_add_same_parity_powers
    {m p a b u v : ℕ} (hm : 3 ≤ m) (hpm : p % m = m - 1)
    (hpos : 0 < a + b) (hlt : a + b < m)
    (hpar : Even u ↔ Even v) :
    ¬ m ∣ a * p ^ u + b * p ^ v := by sorry
