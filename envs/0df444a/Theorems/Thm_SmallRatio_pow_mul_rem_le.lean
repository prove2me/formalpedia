-- Prove2me | Theorems.Thm_SmallRatio_pow_mul_rem_le
-- name    : SmallRatio.pow_mul_rem_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:20:17.070485+00:00
-- url     : https://prove2.me/theorems/ba5901bc-ffe8-5245-ba3b-5a05c1cf4db5
-- title:
--   Small Ratio: pow mul rem le
-- statement:
--   The Small Ratio construction uses the pow mul rem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L212-L226
-- source:
--   https://github.com/jkfarland-bot/SmallRatios/blob/7e757a973e1297239400c90182e1b507ea48b7c0/SmallRatio/Euclid.lean#L212-L226

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc

theorem SmallRatio.pow_mul_rem_le (i : ℕ) (hi : 2 * i ≤ steps k h) :
    2 ^ i * rem k h (2 * i) ≤ k ∧ (2 * i + 1 ≤ steps k h → 2 ^ i * rem k h (2 * i + 1) ≤ k) := by sorry
