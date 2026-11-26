-- Prove2me | Theorems.Thm_QuarterSumLadder_vlam_eq_of_dvd
-- name    : QuarterSumLadder.vlam_eq_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:12:15.862856+00:00
-- url     : https://prove2.me/theorems/d9584bc7-6002-581a-b954-a46f38c7f4b3
-- title:
--   Quarter Sum Ladder: vlam eq of dvd
-- statement:
--   `v_λ(z) = k` from `2^k ∣ N(z)` and `2^{k+1} ∤ N(z)`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L208-L218
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Boundary.lean#L208-L218

module
public import Definitions.Def_QuarterSumLadder_Ladder
public import Definitions.Def_QuarterSumLadder_Boundary
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.vlam_eq_of_dvd {z : GaussianInt} {k : ℕ} (h1 : (2 : ℤ) ^ k ∣ z.norm)
    (h2 : ¬ (2 : ℤ) ^ (k + 1) ∣ z.norm) : vlam z = k := by sorry
