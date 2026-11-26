-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_4
-- name    : Scott1976.DataTypesAsLattices.theorem_6_4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:48.283944+00:00
-- url     : https://prove2.me/theorems/600c1335-8f41-4def-afb0-8c3c059f2f22
-- title:
--   Data Types As Lattices: theorem 6 4
-- statement:
--   **Scott 1976, Theorem 6.4.** `{0}` is the intersection of a closed set
--   with an open set.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L100-L114
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L100-L114

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_6_4 :
    {ofNat 0} = {x : Pomega | x ⊆ ofNat 0} ∩ {x | 0 ∈ x} := by sorry
