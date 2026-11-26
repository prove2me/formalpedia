-- Prove2me | Theorems.Thm_QuarterSumLadder_char_eq_one_iff_pow
-- name    : QuarterSumLadder.char_eq_one_iff_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:57.815791+00:00
-- url     : https://prove2.me/theorems/90a79621-6b10-4cfb-bc71-3bbc1a4be0e8
-- title:
--   Quarter Sum Ladder: char eq one iff pow
-- statement:
--   `χ(x) = 1 ⟺ x^Q = 1` for `x ≠ 0`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L151-L163
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L151-L163

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.char_eq_one_iff_pow {x : ZMod p} (hx : x ≠ 0) : χ x = 1 ↔ x ^ Q p = 1 := by sorry
