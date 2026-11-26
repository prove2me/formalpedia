-- Prove2me | Theorems.Thm_QuarterSumLadder_sq_mod_eight
-- name    : QuarterSumLadder.sq_mod_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:08:39.593245+00:00
-- url     : https://prove2.me/theorems/fe33006d-e0a2-409c-a22c-d7ed5478f237
-- title:
--   Quarter Sum Ladder: sq mod eight
-- statement:
--   Odd squares are `1`, squares of `m ≡ 2 (mod 4)` are `4`, and other squares `0`, modulo `8`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L27-L36
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/WeightTwo.lean#L27-L36

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuarterSumLadder.sq_mod_eight (v : ℕ) :
    (((v : ℤ) ^ 2 : ℤ) : ZMod 8) = (if v % 2 = 1 then 1 else 0) + 4 * (if v % 4 = 2 then 1 else 0) := by sorry
