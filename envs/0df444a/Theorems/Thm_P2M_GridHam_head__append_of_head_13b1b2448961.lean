-- Prove2me | Theorems.Thm_P2M_GridHam_head__append_of_head_13b1b2448961
-- name    : P2M_GridHam_head__append_of_head_13b1b2448961
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:57:13.480277+00:00
-- url     : https://prove2.me/theorems/ed032dc1-b63e-4653-8733-88e276691afe
-- title:
--   P2 M Grid Ham head  append of head 13b1b2448961: P2 M Grid Ham head  append of head 13b1b2448961
-- statement:
--   The P2 M Grid Ham head  append of head 13b1b2448961 construction uses the P2 M Grid Ham head  append of head 13b1b2448961 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L704-L708
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L704-L708

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_head__append_of_head_13b1b2448961 (l M : List Coord) (x : Coord) (h : l.head? = some x) :
    (l ++ M).head? = some x := by sorry

alias «GridHam».«head?_append_of_head» := P2M_GridHam_head__append_of_head_13b1b2448961
