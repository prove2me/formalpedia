-- Prove2me | Theorems.Thm_PascalMinusOne_digitAt_ofDigits_eq_getD
-- name    : PascalMinusOne.digitAt_ofDigits_eq_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:22.665255+00:00
-- url     : https://prove2.me/theorems/1fb49a77-84ab-5521-bec3-f08cd89b8ebb
-- title:
--   Pascal Minus One: digit At of Digits eq get D
-- statement:
--   For a valid base-`p` digit list, `digitAt` of its `ofDigits` value recovers `getD`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L201-L210
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L201-L210

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.digitAt_ofDigits_eq_getD {p i : ℕ} (hp : 2 ≤ p) (L : List ℕ)
    (hL : ∀ d ∈ L, d < p) :
    digitAt p (Nat.ofDigits p L) i = L.getD i 0 := by sorry
