-- Prove2me | Theorems.Thm_SCCThm8_tau_lt_central
-- name    : SCCThm8.tau_lt_central
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:45:00.973312+00:00
-- url     : https://prove2.me/theorems/0d5fd431-c56e-4d9e-ac7f-1eacd1204fb2
-- title:
--   SCCThm8: tau lt central
-- statement:
--   Stretch goal: the group-degeneration bound `C(3k, ⌊3k/2⌋)` exceeds Pratt's threshold for every
--   `k ≥ 1`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L222-L229
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L222-L229

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.tau_lt_central (k : ℕ) (hk : 1 ≤ k) : tau k < Nat.choose (3 * k) (3 * k / 2) := by sorry
