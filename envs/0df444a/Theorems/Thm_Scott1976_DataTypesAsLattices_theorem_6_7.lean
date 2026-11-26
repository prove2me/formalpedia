-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_6_7
-- name    : Scott1976.DataTypesAsLattices.theorem_6_7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:43.272946+00:00
-- url     : https://prove2.me/theorems/6332e9c8-e013-56a6-b897-8f3716601054
-- title:
--   Data Types As Lattices: theorem 6 7
-- statement:
--   **Scott 1976, Theorem 6.7.** Equalizers of continuous maps are
--   countable intersections of Boolean combinations of opens.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L118-L141
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Classification.lean#L118-L141

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_6_7 {f g : Pomega → Pomega}
    (_hf : IsScottContinuous f) (_hg : IsScottContinuous g) :
    {x | f x = g x} =
      ⋂ n, ({x | n ∈ f x ∧ n ∈ g x} ∪ {x | n ∉ f x ∧ n ∉ g x}) := by sorry
