-- Prove2me | Theorems.Thm_SCCThm8_trin_mul_factorial
-- name    : SCCThm8.trin_mul_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:43:57.090649+00:00
-- url     : https://prove2.me/theorems/bb9eb53d-61d5-5e7d-9d4c-813b461f5c36
-- title:
--   SCCThm8: trin mul factorial
-- statement:
--   The SCCThm8 construction uses the trin mul factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L84-L90
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Numeric.lean#L84-L90

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8

theorem SCCThm8.trin_mul_factorial (k : ℕ) : trin k * (k.factorial) ^ 3 = (3 * k).factorial := by sorry
