-- Prove2me | Theorems.Thm_QuarterSumLadder_thirtytwo_dvd_iff
-- name    : QuarterSumLadder.thirtytwo_dvd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:58:13.608841+00:00
-- url     : https://prove2.me/theorems/916d2167-8d21-57f4-aea4-48412a1efa1b
-- title:
--   Quarter Sum Ladder: thirtytwo dvd iff
-- statement:
--   If `4 ∣ x` and `4 ∣ y`, then `32 ∣ x² + y² ↔ 8 ∣ x + y`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L73-L80
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L73-L80

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.thirtytwo_dvd_iff {x y : ℤ} (hx : (4 : ℤ) ∣ x) (hy : (4 : ℤ) ∣ y) :
    (32 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (8 : ℤ) ∣ x + y := by sorry
