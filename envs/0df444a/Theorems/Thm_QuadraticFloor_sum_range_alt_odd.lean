-- Prove2me | Theorems.Thm_QuadraticFloor_sum_range_alt_odd
-- name    : QuadraticFloor.sum_range_alt_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:33.889055+00:00
-- url     : https://prove2.me/theorems/73e2a2c6-1336-5fd9-917a-836919971845
-- title:
--   Quadratic Floor: sum range alt odd
-- statement:
--   An alternating sum over an odd range is `1`.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L25-L31
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L25-L31

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.sum_range_alt_odd (m : ℕ) : ∑ r ∈ range (2 * m + 1), (-1 : ℤ) ^ r = 1 := by sorry
