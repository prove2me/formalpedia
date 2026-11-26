-- Prove2me | Theorems.Thm_QuarterSumLadder_even_quartic_setting
-- name    : QuarterSumLadder.even_quartic_setting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:16:39.138305+00:00
-- url     : https://prove2.me/theorems/1cd2eeb3-107b-5bc9-875a-25b75e0aa240
-- title:
--   Quarter Sum Ladder: even quartic setting
-- statement:
--   **The setting** (Paper IV, §2). For `p ≡ 1 (mod 8)` a quartic `χ` is even, `w = χ(2) = ±1`, and
--   `w = 1` exactly when `2` is a fourth power modulo `p`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L26-L28
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L26-L28

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.even_quartic_setting {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    χ (-1) = 1 ∧ (χ 2 = 1 ∨ χ 2 = -1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) := by sorry
