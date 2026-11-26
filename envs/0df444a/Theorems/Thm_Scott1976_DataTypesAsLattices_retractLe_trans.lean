-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_retractLe_trans
-- name    : Scott1976.DataTypesAsLattices.retractLe_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:07.261193+00:00
-- url     : https://prove2.me/theorems/ed56a9ff-7eba-4e12-8e38-9f41be5b6119
-- title:
--   Data Types As Lattices: retract Le trans
-- statement:
--   The Data Types As Lattices construction uses the retract Le trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L76-L103
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L76-L103

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.retractLe_trans {a b c : Pomega}
    (hab : retractLe a b) (hbc : retractLe b c) :
    a = comp a c ∧ a = comp c a := by sorry
