-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_bot_isRetract
-- name    : Scott1976.DataTypesAsLattices.bot_isRetract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:08.870659+00:00
-- url     : https://prove2.me/theorems/0788b004-5dc4-44b2-a93e-b48e049e7e8e
-- title:
--   Data Types As Lattices: bot is Retract
-- statement:
--   The Data Types As Lattices construction uses the bot is Retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L282-L285
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L282-L285

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.bot_isRetract : IsRetract botElem := by sorry
