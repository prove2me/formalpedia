-- Prove2me | Theorems.Thm_SCCThm8_choose_three_mul_le
-- name    : SCCThm8.choose_three_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:06.974999+00:00
-- url     : https://prove2.me/theorems/6211aeae-5fa8-4ffa-b6e5-5c268f275cd4
-- title:
--   SCCThm8: choose three mul le
-- statement:
--   Entropy bound `C(3k,k) · 4^k ≤ 27^k`, from one term of the binomial expansion of
--   `(k + 2k)^(3k)`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L41-L56
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L41-L56

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.choose_three_mul_le (k : ℕ) : Nat.choose (3 * k) k * 4 ^ k ≤ 27 ^ k := by sorry
