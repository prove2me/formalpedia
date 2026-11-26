-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_gfpBelow_le
-- name    : Scott1976.DataTypesAsLattices.gfpBelow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:27.181613+00:00
-- url     : https://prove2.me/theorems/74bab369-2d7d-5ada-aecc-2bc623aa3dda
-- title:
--   Data Types As Lattices: gfp Below le
-- statement:
--   The Data Types As Lattices construction uses the gfp Below le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L126-L151
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L126-L151

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.gfpBelow_le {f : Pomega → Pomega} (hf : IsScottContinuous f) (b : Pomega)
    (_hb : f b ⊆ b) : gfpBelow f b ⊆ b := by sorry
