-- Prove2me | Theorems.Thm_SCCThm8_two_mul_centralBinom_le
-- name    : SCCThm8.two_mul_centralBinom_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:52.552228+00:00
-- url     : https://prove2.me/theorems/c4c98de6-2c1b-5a2e-be5a-6902aec40d06
-- title:
--   SCCThm8: two mul central Binom le
-- statement:
--   `2 · C(2n,n) ≤ 4^n` for `n ≥ 1`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L24-L29
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L24-L29

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.two_mul_centralBinom_le (n : ℕ) (hn : 1 ≤ n) : 2 * Nat.centralBinom n ≤ 4 ^ n := by sorry
