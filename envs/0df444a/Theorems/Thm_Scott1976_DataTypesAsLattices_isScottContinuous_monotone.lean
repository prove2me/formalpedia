-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
-- name    : Scott1976.DataTypesAsLattices.isScottContinuous_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:07.832305+00:00
-- url     : https://prove2.me/theorems/1b8bb617-b125-4138-8a16-590d16f26036
-- title:
--   Data Types As Lattices: is Scott Continuous monotone
-- statement:
--   The Data Types As Lattices construction uses the is Scott Continuous monotone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L57-L63
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L57-L63

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.isScottContinuous_monotone {f : Pomega → Pomega}
    (hf : IsScottContinuous f) {x y : Pomega} (h : x ⊆ y) : f x ⊆ f y := by sorry
