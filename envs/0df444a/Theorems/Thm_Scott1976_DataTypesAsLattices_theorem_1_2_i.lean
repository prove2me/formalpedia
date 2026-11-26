-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2_i
-- name    : Scott1976.DataTypesAsLattices.theorem_1_2_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:25.796317+00:00
-- url     : https://prove2.me/theorems/bf1e1a25-9a63-5def-be84-7d4730262605
-- title:
--   Data Types As Lattices: theorem 1 2 i
-- statement:
--   **Scott 1976, Theorem 1.2 (i).** `fun(graph(f)) = f` when `f` is continuous.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L63-L76
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L63-L76

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_2_i {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    funOf (graph f) = f := by sorry
