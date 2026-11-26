-- Prove2me | Theorems.Thm_PascalMinusOne_signedZeroSum_zero_left_iff
-- name    : PascalMinusOne.signedZeroSum_zero_left_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:03.622337+00:00
-- url     : https://prove2.me/theorems/659e14a3-8938-55fb-8982-51feea5c136c
-- title:
--   Pascal Minus One: signed Zero Sum zero left iff
-- statement:
--   With no positive tokens, signed zero-sum is ordinary natural divisibility.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L36-L38
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L36-L38

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.signedZeroSum_zero_left_iff (m B : ℕ) :
    SignedZeroSum m 0 B ↔ m ∣ B := by sorry
