-- Prove2me | Theorems.Thm_QuarterSumLadder_gauss_class
-- name    : QuarterSumLadder.gauss_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:06:01.362908+00:00
-- url     : https://prove2.me/theorems/c32711ed-8ead-4970-81b8-b0dff447fa28
-- title:
--   Quarter Sum Ladder: gauss class
-- statement:
--   Gauss's product on the half part of a single class, when `χ(2) = 1`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L184-L212
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L184-L212

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

theorem QuarterSumLadder.gauss_class (hw : χ 2 = 1) {z : GaussianInt} (hz : FourVal z) :
    (2 : ZMod p) ^ (Q p / 2) *
        (-1) ^ (Q p / 2 - ((fiber χ z).filter fun x => 4 * x.val < p).card) = 1 ∧
      ((fiber χ z).filter fun x => 4 * x.val < p).card ≤ Q p / 2 := by sorry
