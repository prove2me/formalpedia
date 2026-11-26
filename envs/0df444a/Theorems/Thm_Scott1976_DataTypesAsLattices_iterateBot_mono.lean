-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_iterateBot_mono
-- name    : Scott1976.DataTypesAsLattices.iterateBot_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:09.756692+00:00
-- url     : https://prove2.me/theorems/2c068585-0e3d-4d75-b7c2-16e207603a06
-- title:
--   Data Types As Lattices: iterate Bot mono
-- statement:
--   The Data Types As Lattices construction uses the iterate Bot mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L135-L140
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/FixedPoint.lean#L135-L140

import Definitions.Def_Scott1976_DataTypesAsLattices_Graph
import Definitions.Def_Scott1976_DataTypesAsLattices_FixedPoint
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.iterateBot_mono {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    ∀ n, iterateBot f n ⊆ iterateBot f (n + 1)
  := by sorry
