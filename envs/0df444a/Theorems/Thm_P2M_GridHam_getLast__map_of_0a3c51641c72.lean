-- Prove2me | Theorems.Thm_P2M_GridHam_getLast__map_of_0a3c51641c72
-- name    : P2M_GridHam_getLast__map_of_0a3c51641c72
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:51:33.315611+00:00
-- url     : https://prove2.me/theorems/4cd69a81-ef2f-42c2-9afc-b314a6a1fd77
-- title:
--   P2 M Grid Ham get Last  map of 0a3c51641c72: P2 M Grid Ham get Last  map of 0a3c51641c72
-- statement:
--   The last element of a mapped list is the image of the last element.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L300-L317
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Forbidden.lean#L300-L317

module
public import Definitions.Def_GridHam_Coloring
public import Definitions.Def_GridHam_Forbidden
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem P2M_GridHam_getLast__map_of_0a3c51641c72 (f : Coord → ℕ) : ∀ (l : List Coord) (t : Coord),
    l.getLast? = some t → (l.map f).getLast? = some (f t) := by sorry

alias «GridHam».«getLast?_map_of» := P2M_GridHam_getLast__map_of_0a3c51641c72
