-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_Icomb_isGraph
-- name    : Scott1976.DataTypesAsLattices.Icomb_isGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:46.546452+00:00
-- url     : https://prove2.me/theorems/fc769ca8-ec17-59fb-869c-c7919e86a2c1
-- title:
--   Data Types As Lattices: Icomb is Graph
-- statement:
--   The Data Types As Lattices construction uses the Icomb is Graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L148-L151
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L148-L151

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.Icomb_isGraph : Icomb = graph (fun x => funOf Icomb x) := by sorry
