-- Prove2me | Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
-- name    : PascalMinusOne.signedZeroSum_one_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:12.691857+00:00
-- url     : https://prove2.me/theorems/ca63e58a-fd1f-5b09-921b-cd8e7c65cc56
-- title:
--   Pascal Minus One: signed Zero Sum one one
-- statement:
--   The Pascal Minus One construction uses the signed Zero Sum one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L21-L22
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L21-L22

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.signedZeroSum_one_one (m : ℕ) : SignedZeroSum m 1 1 := by sorry
