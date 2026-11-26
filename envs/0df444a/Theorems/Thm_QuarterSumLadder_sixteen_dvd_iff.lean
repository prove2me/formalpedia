-- Prove2me | Theorems.Thm_QuarterSumLadder_sixteen_dvd_iff
-- name    : QuarterSumLadder.sixteen_dvd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:57:56.800835+00:00
-- url     : https://prove2.me/theorems/b2465447-285d-5a6a-b69c-ae4afae9404f
-- title:
--   Quarter Sum Ladder: sixteen dvd iff
-- statement:
--   `16 ∣ x² + y² ↔ 4 ∣ x ∧ 4 ∣ y`.
--
--   Source: https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L52-L70
-- source:
--   https://github.com/jkfarland-bot/Quartersumladder/blob/756129d46275e42fb4b27b833d156f2a025a2c21/QuarterSumLadder/Arith.lean#L52-L70

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith
set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder

theorem QuarterSumLadder.sixteen_dvd_iff (x y : ℤ) : (16 : ℤ) ∣ x ^ 2 + y ^ 2 ↔ (4 : ℤ) ∣ x ∧ (4 : ℤ) ∣ y := by sorry
