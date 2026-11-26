-- Prove2me | Theorems.Thm_QuarterSumLadder_kappa_criterion
-- name    : QuarterSumLadder.kappa_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:51.912143+00:00
-- url     : https://prove2.me/theorems/6a1ba2d4-4681-5ef3-8ee9-4d673d35d985
-- title:
--   Quarter Sum Ladder: kappa criterion
-- statement:
--   **The classical criterion** (Paper IV, after Theorem 3.2; Barrucand–Cohn, Williams–Currie):
--   `χ(2) = 1 ⟺ κ ≡ Q (mod 4)`, that is, `h(-4p) ≡ (p - 1)/2 (mod 8)` with `h(-4p) = 2κ`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L379-L390
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L379-L390

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

theorem QuarterSumLadder.kappa_criterion : χ 2 = 1 ↔ kappa p % 4 = (Q p : ℤ) % 4 := by sorry
