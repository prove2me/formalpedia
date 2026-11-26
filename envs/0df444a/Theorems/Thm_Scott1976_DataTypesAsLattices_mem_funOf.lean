-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_mem_funOf
-- name    : Scott1976.DataTypesAsLattices.mem_funOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:51.905975+00:00
-- url     : https://prove2.me/theorems/c02af71d-3f6a-46f2-9b34-c56b1431f589
-- title:
--   Data Types As Lattices: mem fun Of
-- statement:
--   The Data Types As Lattices construction uses the mem fun Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L32-L33
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L32-L33

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.mem_funOf {u x : Pomega} {m : ℕ} :
    m ∈ funOf u x ↔ ∃ n, e n ⊆ x ∧ pair n m ∈ u := by sorry
