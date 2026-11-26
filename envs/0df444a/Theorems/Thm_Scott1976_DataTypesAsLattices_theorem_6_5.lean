-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_5
-- name    : Scott1976.DataTypesAsLattices.theorem_6_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:45.837803+00:00
-- url     : https://prove2.me/theorems/673a0845-7a22-55e9-a10b-2cd586f1bb59
-- title:
--   Data Types As Lattices: theorem 6 5
-- statement:
--   **Scott 1976, Theorem 6.5.** Equalizers `{x | f(x) = a}` split as a
--   closed set intersected with a `Gδ`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L145-L155
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L145-L155

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_6_5 {f : Pomega → Pomega} (_hf : IsScottContinuous f)
    (a : Pomega) :
    {x | f x = a} = {x | a ⊆ f x} ∩ {x | f x ⊆ a} := by sorry
