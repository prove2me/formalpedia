-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_2_5
-- name    : Scott1976.DataTypesAsLattices.eq_2_5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:36.186519+00:00
-- url     : https://prove2.me/theorems/1ffebd00-def1-50e9-b738-3f63985cc112
-- title:
--   Data Types As Lattices: eq 2 5
-- statement:
--   **Scott 1976, (2.5).** `(6 ∪ 10) + 1 = 7 ∪ 11`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L525-L535
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L525-L535

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_2_5 : succSet (ofNat 6 ∪ ofNat 10) = ofNat 7 ∪ ofNat 11 := by sorry
