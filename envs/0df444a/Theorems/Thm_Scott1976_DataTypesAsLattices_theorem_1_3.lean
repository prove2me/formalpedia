-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3
-- name    : Scott1976.DataTypesAsLattices.theorem_1_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:41.827093+00:00
-- url     : https://prove2.me/theorems/048a1142-afb8-4a70-8a7f-174dd993601f
-- title:
--   Data Types As Lattices: theorem 1 3
-- statement:
--   **Scott 1976, Theorem 1.3 (The substitution theorem).** Continuous
--   functions of several variables on `Pω` are closed under substitution.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L66-L69
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L66-L69

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_1_3 {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun x => f (g x)) := by sorry
