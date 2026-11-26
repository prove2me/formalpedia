-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_isScottOpen_basic
-- name    : Scott1976.DataTypesAsLattices.isScottOpen_basic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:38.373083+00:00
-- url     : https://prove2.me/theorems/959be0fc-5522-4c1f-829f-e7d05d0b728f
-- title:
--   Data Types As Lattices: is Scott Open basic
-- statement:
--   The Data Types As Lattices construction uses the is Scott Open basic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L38-L39
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L38-L39

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.isScottOpen_basic (n : ℕ) : IsScottOpen (basicNhhd n) := by sorry
