-- Prove2me | Theorems.Thm_QuarterSumLadder_parity_rho
-- name    : QuarterSumLadder.parity_rho
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:07:38.16058+00:00
-- url     : https://prove2.me/theorems/7e6892f1-3d2f-44c6-affa-5b6eb28cbbc4
-- title:
--   Quarter Sum Ladder: parity rho
-- statement:
--   The indicator `[2^{(p-1)/8} = -1]` through `ρ = ord_p(2)`, when `2` is a fourth power.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L268-L311
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Counts.lean#L268-L311

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

theorem QuarterSumLadder.parity_rho (hw : χ 2 = 1) :
    (if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 =
      (if 2 ∣ orderOf (2 : ZMod p) then (p - 1) / (4 * orderOf (2 : ZMod p)) else 0) % 2 := by sorry
