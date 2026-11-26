-- Prove2me | Theorems.Thm_QuarterSumLadder_E_add_R
-- name    : QuarterSumLadder.E_add_R
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:09:08.360897+00:00
-- url     : https://prove2.me/theorems/2a241457-1719-5867-b726-a1323aca45ce
-- title:
--   Quarter Sum Ladder: E add R
-- statement:
--   `E_z + #{0 < m < p/4 : χ(m) = z} = Q/2`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L200-L214
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L200-L214

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ

theorem QuarterSumLadder.E_add_R {z : GaussianInt} (hz : FourVal z) :
    E χ z + ((fiber χ z).filter fun x => 4 * x.val < p).card = Q p / 2 := by sorry
