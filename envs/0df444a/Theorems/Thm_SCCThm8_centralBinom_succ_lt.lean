-- Prove2me | Theorems.Thm_SCCThm8_centralBinom_succ_lt
-- name    : SCCThm8.centralBinom_succ_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:49.530825+00:00
-- url     : https://prove2.me/theorems/35713347-fffa-4de3-9f51-0f67e57ddc10
-- title:
--   SCCThm8: central Binom succ lt
-- statement:
--   `C(n+1, ⌊(n+1)/2⌋)`-free step: `centralBinom (n+1) < 4 · centralBinom n`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L16-L21
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L16-L21

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.centralBinom_succ_lt (n : ℕ) : Nat.centralBinom (n + 1) < 4 * Nat.centralBinom n := by sorry
