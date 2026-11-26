-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_funOf_monotone_right
-- name    : Scott1976.DataTypesAsLattices.funOf_monotone_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:30.21281+00:00
-- url     : https://prove2.me/theorems/1a05a9cf-ddfa-4df9-8ae6-bb8b45a2826c
-- title:
--   Data Types As Lattices: fun Of monotone right
-- statement:
--   The Data Types As Lattices construction uses the fun Of monotone right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L35-L39
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L35-L39

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.funOf_monotone_right (u : Pomega) {x y : Pomega} (h : x ⊆ y) :
    funOf u x ⊆ funOf u y := by sorry
