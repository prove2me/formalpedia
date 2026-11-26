-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_6
-- name    : Scott1976.DataTypesAsLattices.theorem_6_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:49.121947+00:00
-- url     : https://prove2.me/theorems/58203e3d-0999-43a2-9346-e10544347f97
-- title:
--   Data Types As Lattices: theorem 6 6
-- statement:
--   **Scott 1976, Theorem 6.6.** Membership of `f(x)` in a finite family
--   is a union of equalizers.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L159-L163
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L159-L163

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_6_6 {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (E : Set Pomega) :
    {x | f x ∈ E} = ⋃ e ∈ E, {x | f x = e} := by sorry
