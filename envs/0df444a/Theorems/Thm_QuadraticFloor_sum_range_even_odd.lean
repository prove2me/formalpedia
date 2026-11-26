-- Prove2me | Theorems.Thm_QuadraticFloor_sum_range_even_odd
-- name    : QuadraticFloor.sum_range_even_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:44:06.363856+00:00
-- url     : https://prove2.me/theorems/91bc5980-b924-4c76-a381-298c504c700c
-- title:
--   Quadratic Floor: sum range even odd
-- statement:
--   The even terms of a sum over an odd range.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L34-L43
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/RootCount.lean#L34-L43

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.sum_range_even_odd {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ r ∈ range (2 * m + 1), (if Even r then f r else 0) = ∑ j ∈ range (m + 1), f (2 * j) := by sorry
