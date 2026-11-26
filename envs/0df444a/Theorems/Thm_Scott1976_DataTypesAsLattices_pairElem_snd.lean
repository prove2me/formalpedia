-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_pairElem_snd
-- name    : Scott1976.DataTypesAsLattices.pairElem_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:54.055464+00:00
-- url     : https://prove2.me/theorems/7fc91133-36df-5e8d-8844-5181534cdf36
-- title:
--   Data Types As Lattices: pair Elem snd
-- statement:
--   The Data Types As Lattices construction uses the pair Elem snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L22-L23
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L22-L23

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.pairElem_snd (x y : Pomega) : funOf (pairElem x y) (ofNat 1) = y := by sorry
