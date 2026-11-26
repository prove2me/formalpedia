-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_3
-- name    : Scott1976.DataTypesAsLattices.theorem_6_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:34.674831+00:00
-- url     : https://prove2.me/theorems/8a15afbe-4067-5db0-aa30-777b452cd0f1
-- title:
--   Data Types As Lattices: theorem 6 3
-- statement:
--   **Scott 1976, Theorem 6.3.** `{x | f(x) = ⊤}` is a countable
--   intersection of Scott-open sets.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L83-L96
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L83-L96

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_6_3 {f : Pomega → Pomega} (_hf : IsScottContinuous f) :
    {x | f x = topElem} = ⋂ n, {x | n ∈ f x} := by sorry
