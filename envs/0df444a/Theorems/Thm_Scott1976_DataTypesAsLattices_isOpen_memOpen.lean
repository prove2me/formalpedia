-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_isOpen_memOpen
-- name    : Scott1976.DataTypesAsLattices.isOpen_memOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:38.780136+00:00
-- url     : https://prove2.me/theorems/a53e568e-9b67-5e11-91de-53e798f880b2
-- title:
--   Data Types As Lattices: is Open mem Open
-- statement:
--   The Data Types As Lattices construction uses the is Open mem Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L140-L141
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Continuous.lean#L140-L141

import Mathlib.Topology.Order
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Definitions.Def_Scott1976_DataTypesAsLattices_Continuous
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.isOpen_memOpen (k : ℕ) : IsOpen (memOpen k) := by sorry
