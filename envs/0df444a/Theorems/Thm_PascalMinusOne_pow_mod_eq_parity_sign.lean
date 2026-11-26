-- Prove2me | Theorems.Thm_PascalMinusOne_pow_mod_eq_parity_sign
-- name    : PascalMinusOne.pow_mod_eq_parity_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:29.567941+00:00
-- url     : https://prove2.me/theorems/838fe674-2efc-4277-bfe6-bd17f0187219
-- title:
--   Pascal Minus One: pow mod eq parity sign
-- statement:
--   Convert `p % m = m-1` into alternating signs for powers of `p`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L18-L51
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L18-L51

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.pow_mod_eq_parity_sign {m p i : ℕ} (hm : 2 ≤ m) (hpm : p % m = m - 1) :
    p ^ i % m = if Even i then 1 else m - 1 := by sorry
