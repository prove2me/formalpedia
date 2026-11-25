-- Prove2me | Theorems.Thm_SCCThm8_two_mul_choose_lt
-- name    : SCCThm8.two_mul_choose_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:00.513129+00:00
-- url     : https://prove2.me/theorems/7656673e-ffa2-49e5-a15a-bf7ff5259b96
-- title:
--   SCCThm8: two mul choose lt
-- statement:
--   `2 · C(2k,k) < 4^k` for `k ≥ 2`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L32-L37
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L32-L37

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.two_mul_choose_lt (k : ℕ) (hk : 2 ≤ k) : 2 * Nat.choose (2 * k) k < 4 ^ k := by sorry
