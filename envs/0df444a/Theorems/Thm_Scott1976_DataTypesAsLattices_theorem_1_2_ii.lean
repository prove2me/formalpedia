-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_ii
-- name    : Scott1976.DataTypesAsLattices.theorem_1_2_ii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:43.321086+00:00
-- url     : https://prove2.me/theorems/edeb0bb6-81de-5510-85c7-1fc60c758d9b
-- title:
--   Data Types As Lattices: theorem 1 2 ii
-- statement:
--   **Scott 1976, Theorem 1.2 (ii).** `u ⊆ graph(fun(u))`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L79-L82
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L79-L82

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_2_ii (u : Pomega) : u ⊆ graph (funOf u) := by sorry
