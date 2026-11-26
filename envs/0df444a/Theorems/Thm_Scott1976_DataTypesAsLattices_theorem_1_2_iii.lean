-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_iii
-- name    : Scott1976.DataTypesAsLattices.theorem_1_2_iii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:50.276506+00:00
-- url     : https://prove2.me/theorems/63aa1a5c-8bad-5968-9118-4ef2af8fb627
-- title:
--   Data Types As Lattices: theorem 1 2 iii
-- statement:
--   The Data Types As Lattices construction uses the theorem 1 2 iii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L89-L108
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L89-L108

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_2_iii (u : Pomega) :
    graph (funOf u) = u ↔ IsGraph u := by sorry
