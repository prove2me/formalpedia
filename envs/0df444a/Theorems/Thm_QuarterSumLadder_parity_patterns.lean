-- Prove2me | Theorems.Thm_QuarterSumLadder_parity_patterns
-- name    : QuarterSumLadder.parity_patterns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:17:08.860623+00:00
-- url     : https://prove2.me/theorems/6db8fd75-67f5-5d54-bbdc-53160407acc6
-- title:
--   Quarter Sum Ladder: parity patterns
-- statement:
--   **The excluded patterns** (Paper IV, Corollary 3.4, first statement): the parity vector of
--   `(R₀, R₁, R₂, R₃)` is never `1010` or `0101`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L87-L90
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/Solution.lean#L87-L90

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.parity_patterns {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    ¬ (R χ 0 % 2 = 1 ∧ R χ 1 % 2 = 0 ∧ R χ 2 % 2 = 1 ∧ R χ 3 % 2 = 0) ∧
      ¬ (R χ 0 % 2 = 0 ∧ R χ 1 % 2 = 1 ∧ R χ 2 % 2 = 0 ∧ R χ 3 % 2 = 1) := by sorry
