-- Prove2me | Theorems.Thm_P2M_PascalMinusOne_getD_le_of_forall__67768b8a94b6
-- name    : P2M_PascalMinusOne_getD_le_of_forall__67768b8a94b6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:32.327566+00:00
-- url     : https://prove2.me/theorems/00bbaf94-7841-53b2-9218-de7cc9895fc3
-- title:
--   P2 M Pascal Minus One get D le of forall  67768b8a94b6: P2 M Pascal Minus One get D le of forall  67768b8a94b6
-- statement:
--   Componentwise list comparison can be read through `getD`, including past the end.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L227-L235
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L227-L235

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem P2M_PascalMinusOne_getD_le_of_forall__67768b8a94b6 {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) (i : ℕ) :
    S.getD i 0 ≤ D.getD i 0 := by sorry

alias «PascalMinusOne».«getD_le_of_forall₂» := P2M_PascalMinusOne_getD_le_of_forall__67768b8a94b6
