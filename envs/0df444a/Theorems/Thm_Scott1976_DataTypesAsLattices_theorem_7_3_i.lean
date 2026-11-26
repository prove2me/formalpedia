-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_7_3_i
-- name    : Scott1976.DataTypesAsLattices.theorem_7_3_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:04:01.372295+00:00
-- url     : https://prove2.me/theorems/46fdfe81-41d9-4f99-b5cc-c2cd0c335d4c
-- title:
--   Data Types As Lattices: theorem 7 3 i
-- statement:
--   **Scott 1976, Theorem 7.3 (i).** `I : A → A`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L154-L156
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L154-L156

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_7_3_i (A : RestrictedEquiv) :
    (arrowE A A).mem Icomb := by sorry
