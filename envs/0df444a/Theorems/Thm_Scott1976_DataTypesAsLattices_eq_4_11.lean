-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_4_11
-- name    : Scott1976.DataTypesAsLattices.eq_4_11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:52.796855+00:00
-- url     : https://prove2.me/theorems/9f477a63-7af7-4c94-b125-2f942f943801
-- title:
--   Data Types As Lattices: eq 4 11
-- statement:
--   **Scott 1976, (4.11).** Action of composed function-space retracts.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L219-L222
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L219-L222

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_4_11 (a b a' b' u : Pomega) :
    funOf (arrowR a b) (funOf (arrowR a' b') u) =
      comp b (comp (comp b' (comp u a')) a) := by sorry
