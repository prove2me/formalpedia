-- Prove2me | Theorems.Thm_P2M_GridHam_head__map_of_95c870c06cfa
-- name    : P2M_GridHam_head__map_of_95c870c06cfa
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:10:30.916058+00:00
-- url     : https://prove2.me/theorems/5ce90cc5-738f-4569-a1bd-c2aaf8eb1996
-- title:
--   P2 M Grid Ham head  map of 95c870c06cfa: P2 M Grid Ham head  map of 95c870c06cfa
-- statement:
--   The P2 M Grid Ham head  map of 95c870c06cfa construction uses the P2 M Grid Ham head  map of 95c870c06cfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L573-L580
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/F3.lean#L573-L580

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_head__map_of_95c870c06cfa (f : Coord → Coord) (l : List Coord) (x : Coord)
    (h : l.head? = some x) : (l.map f).head? = some (f x) := by sorry

alias «GridHam».«head?_map_of» := P2M_GridHam_head__map_of_95c870c06cfa
