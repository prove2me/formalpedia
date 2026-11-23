-- Prove2me | Theorems.Thm_Vector_sum_four
-- name    : Vector.sum_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:39:37.967242+00:00
-- url     : https://prove2.me/theorems/3991cb54-a42d-4eef-aa09-08fc5e666907
-- title:
--   Vector: sum four
-- statement:
--   The sum of a length-4 vector equals the sum of its components.
--
--   Source: https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Utils.lean#L49-L52
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Utils.lean#L49-L52

module
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic
public import Definitions.Def_Apportionmentlib_Utils
set_option autoImplicit false
@[expose] public section
public section

theorem Vector.sum_four (v : Vector ℕ 4) : v.sum = v[0] + v[1] + v[2] + v[3] := by sorry
