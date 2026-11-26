-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_4
-- name    : Scott1976.DataTypesAsLattices.theorem_1_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:55.132893+00:00
-- url     : https://prove2.me/theorems/97f96fa4-f740-4a2e-97ca-c2e279144124
-- title:
--   Data Types As Lattices: theorem 1 4
-- statement:
--   **Scott 1976, Theorem 1.4 (The fixed-point theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L143-L168
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L143-L168

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_4 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    f (fix f) = fix f ∧ ∀ x, f x = x → fix f ⊆ x := by sorry
