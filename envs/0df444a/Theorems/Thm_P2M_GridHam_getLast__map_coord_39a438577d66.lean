-- Prove2me | Theorems.Thm_P2M_GridHam_getLast__map_coord_39a438577d66
-- name    : P2M_GridHam_getLast__map_coord_39a438577d66
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:28:01.61761+00:00
-- url     : https://prove2.me/theorems/8eddcedb-fbc0-4023-a0c1-0240775418d7
-- title:
--   P2 M Grid Ham get Last  map coord 39a438577d66: P2 M Grid Ham get Last  map coord 39a438577d66
-- statement:
--   The last element of a mapped list (coordinate-valued version).
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L161-L178
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/StripSplit.lean#L161-L178

module
public import Definitions.Def_GridHam_Forbidden
public import Definitions.Def_GridHam_StripSplit
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_getLast__map_coord_39a438577d66 (f : Coord → Coord) : ∀ (l : List Coord) (t : Coord),
    l.getLast? = some t → (l.map f).getLast? = some (f t) := by sorry

alias «GridHam».«getLast?_map_coord» := P2M_GridHam_getLast__map_coord_39a438577d66
