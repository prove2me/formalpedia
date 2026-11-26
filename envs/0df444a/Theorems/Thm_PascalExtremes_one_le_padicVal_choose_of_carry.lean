-- Prove2me | Theorems.Thm_PascalExtremes_one_le_padicVal_choose_of_carry
-- name    : PascalExtremes.one_le_padicVal_choose_of_carry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:55:58.301248+00:00
-- url     : https://prove2.me/theorems/68fceec0-9f23-4571-b0b1-1ac8a3300593
-- title:
--   Pascal Extremes: one le padic Val choose of carry
-- statement:
--   One actual carry gives positive `p`-adic valuation.
--
--   Source: https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/CarryBounds.lean#L13-L28
-- source:
--   https://github.com/jfairfaxball-348/Pascal-Extremes/blob/a7e414a9e5bcf931c79b2bd4d4ffa81eeb6cfc22/PascalExtremes/CarryBounds.lean#L13-L28

module
public import Definitions.Def_PascalExtremes_Kummer
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public import Definitions.Def_PascalExtremes_CarryBounds
set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes

theorem PascalExtremes.one_le_padicVal_choose_of_carry
    {p n k i : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hi : 1 ≤ i)
    (hcarry : CarryAt p n k i) :
    1 ≤ padicValNat p (n.choose k) := by sorry
