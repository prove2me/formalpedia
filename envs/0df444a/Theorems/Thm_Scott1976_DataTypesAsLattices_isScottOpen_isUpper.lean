-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_isScottOpen_isUpper
-- name    : Scott1976.DataTypesAsLattices.isScottOpen_isUpper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:28.973346+00:00
-- url     : https://prove2.me/theorems/449100ca-5cc1-59a1-aca5-f7c443a28d19
-- title:
--   Data Types As Lattices: is Scott Open is Upper
-- statement:
--   Open sets are upper sets: if `x ∈ U` and `x ⊆ y` then `y ∈ U`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L42-L46
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L42-L46

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.isScottOpen_isUpper {U : Set Pomega} (hU : IsScottOpen U)
    {x y : Pomega} (hx : x ∈ U) (hxy : x ⊆ y) : y ∈ U := by sorry
