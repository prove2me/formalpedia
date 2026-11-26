-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_2_6
-- name    : Scott1976.DataTypesAsLattices.eq_2_6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:41.423798+00:00
-- url     : https://prove2.me/theorems/d449e258-54ce-4d94-8955-a02c55c403c9
-- title:
--   Data Types As Lattices: eq 2 6
-- statement:
--   **Scott 1976, (2.6).** `0 − 1 = ⊥`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L538-L540
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L538-L540

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_2_6 : predSet (ofNat 0) = botElem := by sorry
