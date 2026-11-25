-- Prove2me | Theorems.Thm_SCCThm8_choose_odd_step
-- name    : SCCThm8.choose_odd_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:57.421947+00:00
-- url     : https://prove2.me/theorems/02c55b40-433f-440e-a400-cd30ebe42031
-- title:
--   SCCThm8: choose odd step
-- statement:
--   `C(2m+1, m) · (m+1) = (2m+1) · C(2m, m)`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L110-L114
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L110-L114

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.choose_odd_step (m : ℕ) :
    Nat.choose (2 * m + 1) m * (m + 1) = (2 * m + 1) * Nat.choose (2 * m) m := by sorry
