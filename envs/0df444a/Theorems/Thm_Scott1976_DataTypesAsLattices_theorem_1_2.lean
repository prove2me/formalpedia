-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_2
-- name    : Scott1976.DataTypesAsLattices.theorem_1_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:01.977713+00:00
-- url     : https://prove2.me/theorems/25dfddf8-442f-4d3a-9b87-2068d4b519a7
-- title:
--   Data Types As Lattices: theorem 1 2
-- statement:
--   **Scott 1976, Theorem 1.2 (The graph theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L111-L114
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Graph.lean#L111-L114

import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_2 {f : Pomega → Pomega} (hf : IsScottContinuous f) (u : Pomega) :
    funOf (graph f) = f ∧ u ⊆ graph (funOf u) ∧
      (graph (funOf u) = u ↔ IsGraph u) := by sorry
