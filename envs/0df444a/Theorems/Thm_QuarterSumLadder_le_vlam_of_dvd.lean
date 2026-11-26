-- Prove2me | Theorems.Thm_QuarterSumLadder_le_vlam_of_dvd
-- name    : QuarterSumLadder.le_vlam_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:23.361339+00:00
-- url     : https://prove2.me/theorems/8f7d79e2-3e31-5361-aab2-11205c46808c
-- title:
--   Quarter Sum Ladder: le vlam of dvd
-- statement:
--   `k ≤ v_λ(z)` from `2^k ∣ N(z)`, for `z ≠ 0`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L221-L227
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L221-L227

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.le_vlam_of_dvd {z : GaussianInt} (hz : z ≠ 0) {k : ℕ} (h1 : (2 : ℤ) ^ k ∣ z.norm) :
    k ≤ vlam z := by sorry
