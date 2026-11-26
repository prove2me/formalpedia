-- Prove2me | Theorems.Thm_P2M_PascalMinusOne_sum_le_of_forall__a2453d65e7c8
-- name    : P2M_PascalMinusOne_sum_le_of_forall__a2453d65e7c8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:26.726694+00:00
-- url     : https://prove2.me/theorems/97a91ecc-39b0-5bb2-8d7c-2762c02fb359
-- title:
--   P2 M Pascal Minus One sum le of forall  a2453d65e7c8: P2 M Pascal Minus One sum le of forall  a2453d65e7c8
-- statement:
--   Componentwise comparison also compares ordinary digit sums.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L161-L167
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/MinusOne.lean#L161-L167

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Definitions.Def_PascalMinusOne_Kummer
import Definitions.Def_PascalMinusOne_SignedTokens
import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.List.GetD
import Definitions.Def_PascalMinusOne_MinusOne
set_option autoImplicit true
open PascalMinusOne

theorem P2M_PascalMinusOne_sum_le_of_forall__a2453d65e7c8 {S D : List ℕ}
    (h : List.Forall₂ (· ≤ ·) S D) : S.sum ≤ D.sum := by sorry

alias «PascalMinusOne».«sum_le_of_forall₂» := P2M_PascalMinusOne_sum_le_of_forall__a2453d65e7c8
