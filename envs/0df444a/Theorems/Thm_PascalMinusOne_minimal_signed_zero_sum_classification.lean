-- Prove2me | Theorems.Thm_PascalMinusOne_minimal_signed_zero_sum_classification
-- name    : PascalMinusOne.minimal_signed_zero_sum_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:19:09.913946+00:00
-- url     : https://prove2.me/theorems/f03e9f03-d646-42f7-b5af-ca95153eca93
-- title:
--   Pascal Minus One: minimal signed zero sum classification
-- statement:
--   Minimal zero-sum signed-token classification for `m ≥ 3`.
--
--   Source: https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L41-L114
-- source:
--   https://github.com/jfairfaxball-348/pascal-minus-one/blob/5f20593464d86ef8c3c34e1c00d84f8a48c0457e/PascalMinusOne/SignedTokens.lean#L41-L114

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
set_option autoImplicit true
open PascalMinusOne

theorem PascalMinusOne.minimal_signed_zero_sum_classification {m A B : ℕ} (hm : 3 ≤ m) :
    MinimalSignedZeroSum m A B ↔
      (A = 1 ∧ B = 1) ∨ (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) := by sorry
