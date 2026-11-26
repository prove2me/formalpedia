-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_left
-- name    : Scott1976.DataTypesAsLattices.funOf_monotone_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:25.690975+00:00
-- url     : https://prove2.me/theorems/1e0cb145-6f9c-4a73-80dd-d988e6688012
-- title:
--   Data Types As Lattices: fun Of monotone left
-- statement:
--   The Data Types As Lattices construction uses the fun Of monotone left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L41-L45
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L41-L45

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.funOf_monotone_left {u v : Pomega} (h : u ⊆ v) (x : Pomega) :
    funOf u x ⊆ funOf v x := by sorry
