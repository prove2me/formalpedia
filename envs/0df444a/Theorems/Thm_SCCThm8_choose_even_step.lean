-- Prove2me | Theorems.Thm_SCCThm8_choose_even_step
-- name    : SCCThm8.choose_even_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:47.836486+00:00
-- url     : https://prove2.me/theorems/2cf0c1bb-5843-526a-b5c7-276847e91553
-- title:
--   SCCThm8: choose even step
-- statement:
--   `C(2m+2, m+1) = 2 · C(2m+1, m)`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L117-L120
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L117-L120

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.choose_even_step (m : ℕ) :
    Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by sorry
