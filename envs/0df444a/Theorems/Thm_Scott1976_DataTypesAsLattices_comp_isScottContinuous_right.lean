-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_comp_isScottContinuous_right
-- name    : Scott1976.DataTypesAsLattices.comp_isScottContinuous_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:05.846705+00:00
-- url     : https://prove2.me/theorems/3d1dcf7f-fc28-4b7c-8abb-0cc4caa6f88e
-- title:
--   Data Types As Lattices: comp is Scott Continuous right
-- statement:
--   The Data Types As Lattices construction uses the comp is Scott Continuous right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L21-L24
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L21-L24

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.comp_isScottContinuous_right (u : Pomega) :
    IsScottContinuous (fun v => comp u v) := by sorry
