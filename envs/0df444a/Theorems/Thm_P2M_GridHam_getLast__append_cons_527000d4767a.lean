-- Prove2me | Theorems.Thm_P2M_GridHam_getLast__append_cons_527000d4767a
-- name    : P2M_GridHam_getLast__append_cons_527000d4767a
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:28:09.823777+00:00
-- url     : https://prove2.me/theorems/045cf8c3-d6e8-4792-9d39-6aa3c31c0d41
-- title:
--   P2 M Grid Ham get Last  append cons 527000d4767a: P2 M Grid Ham get Last  append cons 527000d4767a
-- statement:
--   The last element of `l1 ++ (c :: m)` is the last element of `c :: m`.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L146-L158
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L146-L158

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_getLast__append_cons_527000d4767a : ∀ (l1 : List Coord) (c : Coord) (m : List Coord),
    (l1 ++ c :: m).getLast? = (c :: m).getLast? := by sorry

alias «GridHam».«getLast?_append_cons» := P2M_GridHam_getLast__append_cons_527000d4767a
