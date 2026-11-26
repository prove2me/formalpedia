-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_3_2_i
-- name    : Scott1976.DataTypesAsLattices.theorem_3_2_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:05.1618+00:00
-- url     : https://prove2.me/theorems/4287a77b-71df-5fe9-ae10-21894b167836
-- title:
--   Data Types As Lattices: theorem 3 2 i
-- statement:
--   **Scott 1976, Theorem 3.2 (i).** The zero test selects `G`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L41-L49
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Enumeration.lean#L41-L49

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_3_2_i : condSet (ofNat 0) Gcomb botElem = Gcomb := by sorry
