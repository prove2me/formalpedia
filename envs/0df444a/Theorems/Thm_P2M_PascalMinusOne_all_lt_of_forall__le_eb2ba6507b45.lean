-- Prove2me | Theorems.Thm_P2M_PascalMinusOne_all_lt_of_forall__le_eb2ba6507b45
-- name    : P2M_PascalMinusOne_all_lt_of_forall__le_eb2ba6507b45
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:44.177951+00:00
-- url     : https://prove2.me/theorems/1dbd2537-9c83-44f3-ace2-736515a67811
-- title:
--   P2 M Pascal Minus One all lt of forall  le eb2ba6507b45: P2 M Pascal Minus One all lt of forall  le eb2ba6507b45
-- statement:
--   A componentwise subdigit list inherits the base bound from the ambient digit list.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L213-L224
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L213-L224

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem P2M_PascalMinusOne_all_lt_of_forall__le_eb2ba6507b45 {S D : List ℕ} {p : ℕ}
    (h : List.Forall₂ (· ≤ ·) S D)
    (hD : ∀ d ∈ D, d < p) :
    ∀ s ∈ S, s < p := by sorry

alias «PascalMinusOne».«all_lt_of_forall₂_le» := P2M_PascalMinusOne_all_lt_of_forall__le_eb2ba6507b45
