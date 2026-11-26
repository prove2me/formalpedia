-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_determined
-- name    : Scott1976.DataTypesAsLattices.isScottContinuous_determined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:41.575717+00:00
-- url     : https://prove2.me/theorems/579be58e-47e4-4fb6-9818-b86bb1e0eccc
-- title:
--   Data Types As Lattices: is Scott Continuous determined
-- statement:
--   Continuous functions are determined by their values on finite sets.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L125-L130
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L125-L130

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.isScottContinuous_determined {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g)
    (hfin : ∀ n, f (e n) = g (e n)) : f = g := by sorry
