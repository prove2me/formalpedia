-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_pairElem_fst
-- name    : Scott1976.DataTypesAsLattices.pairElem_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:50.846262+00:00
-- url     : https://prove2.me/theorems/6a21133d-df96-51aa-8d21-8e966121b8b5
-- title:
--   Data Types As Lattices: pair Elem fst
-- statement:
--   The Data Types As Lattices construction uses the pair Elem fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L19-L20
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L19-L20

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.pairElem_fst (x y : Pomega) : funOf (pairElem x y) (ofNat 0) = x := by sorry
