-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_comp_right_const
-- name    : Scott1976.DataTypesAsLattices.comp_right_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:13.464976+00:00
-- url     : https://prove2.me/theorems/1fa98b5c-0e2e-40e3-a6d5-74eaf3754633
-- title:
--   Data Types As Lattices: comp right const
-- statement:
--   The Data Types As Lattices construction uses the comp right const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L196-L199
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L196-L199

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.comp_right_const (a : Pomega) :
    IsScottContinuous (fun u => comp u a) := by sorry
