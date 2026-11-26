-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3_comp
-- name    : Scott1976.DataTypesAsLattices.theorem_1_3_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:52.567695+00:00
-- url     : https://prove2.me/theorems/5e764a0f-d613-59b9-93a3-d6d1f993274a
-- title:
--   Data Types As Lattices: theorem 1 3 comp
-- statement:
--   **Scott 1976, Theorem 1.3, composition.**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L42-L62
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L42-L62

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_3_comp {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (f ∘ g) := by sorry
