-- Prove2me | Theorems.Thm_SCCThm8_tau_lt_two_pow
-- name    : SCCThm8.tau_lt_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:44:45.056455+00:00
-- url     : https://prove2.me/theorems/606f2187-f0d2-4be9-8aca-7b68914a2efe
-- title:
--   SCCThm8: tau lt two pow
-- statement:
--   The group-restriction bound `2^(3k-1)` exceeds Pratt's threshold for every `k ≥ 2`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L59-L77
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L59-L77

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.tau_lt_two_pow (k : ℕ) (hk : 2 ≤ k) : tau k < 2 ^ (3 * k - 1) := by sorry
