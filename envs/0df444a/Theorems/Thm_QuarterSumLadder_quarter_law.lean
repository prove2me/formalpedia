-- Prove2me | Theorems.Thm_QuarterSumLadder_quarter_law
-- name    : QuarterSumLadder.quarter_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:05:49.584933+00:00
-- url     : https://prove2.me/theorems/bf144014-3732-55b3-819d-42842b681b51
-- title:
--   Quarter Sum Ladder: quarter law
-- statement:
--   **The quarter law** (the quartic Gauss lemma): `χ(2) = (-1)^{R₁ + R₃}`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L172-L181
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L172-L181

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

theorem QuarterSumLadder.quarter_law : χ 2 = (-1) ^ (R χ 1 + R χ 3) := by sorry
