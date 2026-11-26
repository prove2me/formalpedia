-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_graph
-- name    : Scott1976.DataTypesAsLattices.mem_graph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:42.671586+00:00
-- url     : https://prove2.me/theorems/bffd8456-a365-5fda-b69a-55b3a7f76b57
-- title:
--   Data Types As Lattices: mem graph
-- statement:
--   The Data Types As Lattices construction uses the mem graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L29-L30
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L29-L30

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mem_graph {f : Pomega → Pomega} {p : ℕ} :
    p ∈ graph f ↔ ∃ n m, p = pair n m ∧ m ∈ f (e n) := by sorry
