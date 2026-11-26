-- Prove2me | Theorems.Thm_P2M_PascalMinusOne_ofDigits_le_of_forall__1f91a730a18e
-- name    : P2M_PascalMinusOne_ofDigits_le_of_forall__1f91a730a18e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:17.575623+00:00
-- url     : https://prove2.me/theorems/04ad9b24-8a81-59b8-9e82-d78df4564763
-- title:
--   P2 M Pascal Minus One of Digits le of forall  1f91a730a18e: P2 M Pascal Minus One of Digits le of forall  1f91a730a18e
-- statement:
--   Componentwise comparison of equal-length digit lists is respected by `Nat.ofDigits`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L151-L158
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L151-L158

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem P2M_PascalMinusOne_ofDigits_le_of_forall__1f91a730a18e (p : ℕ) {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) :
    Nat.ofDigits p S ≤ Nat.ofDigits p D := by sorry

alias «PascalMinusOne».«ofDigits_le_of_forall₂» := P2M_PascalMinusOne_ofDigits_le_of_forall__1f91a730a18e
