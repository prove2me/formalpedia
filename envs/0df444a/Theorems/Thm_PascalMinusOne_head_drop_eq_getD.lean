-- Prove2me | Theorems.Thm_PascalMinusOne_head_drop_eq_getD
-- name    : PascalMinusOne.head_drop_eq_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:28.762705+00:00
-- url     : https://prove2.me/theorems/973bc0bb-5a65-580d-a092-2bfc6df37585
-- title:
--   Pascal Minus One: head drop eq get D
-- statement:
--   The head of the `i`-fold tail, with default zero, is `List.getD i 0`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L190-L198
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L190-L198

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.head_drop_eq_getD (L : List ℕ) (i : ℕ) :
    (L.drop i).head! = L.getD i 0 := by sorry
