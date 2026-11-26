-- Prove2me | Theorems.Thm_QuarterSumLadder_patterns_excluded
-- name    : QuarterSumLadder.patterns_excluded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:44.361966+00:00
-- url     : https://prove2.me/theorems/71678277-ec9c-40cc-a486-dfe725f5d535
-- title:
--   Quarter Sum Ladder: patterns excluded
-- statement:
--   **The excluded patterns** (Paper IV, Corollary 3.4): the parity vector of
--   `(R₀, R₁, R₂, R₃)` is never `1010` or `0101`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L315-L328
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L315-L328

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

theorem QuarterSumLadder.patterns_excluded :
    ¬ (R χ 0 % 2 = 1 ∧ R χ 1 % 2 = 0 ∧ R χ 2 % 2 = 1 ∧ R χ 3 % 2 = 0) ∧
      ¬ (R χ 0 % 2 = 0 ∧ R χ 1 % 2 = 1 ∧ R χ 2 % 2 = 0 ∧ R χ 3 % 2 = 1) := by sorry
