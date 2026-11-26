-- Prove2me | Theorems.Thm_PascalMinusOne_signedZeroSum_right_zero_iff
-- name    : PascalMinusOne.signedZeroSum_right_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:04.994882+00:00
-- url     : https://prove2.me/theorems/b6913f99-fc33-4ce9-a349-3eccac4c7e8e
-- title:
--   Pascal Minus One: signed Zero Sum right zero iff
-- statement:
--   With no negative tokens, signed zero-sum is ordinary natural divisibility.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L31-L33
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L31-L33

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.signedZeroSum_right_zero_iff (m A : ℕ) :
    SignedZeroSum m A 0 ↔ m ∣ A := by sorry
