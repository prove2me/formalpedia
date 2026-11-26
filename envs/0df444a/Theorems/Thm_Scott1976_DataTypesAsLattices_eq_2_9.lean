-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_2_9
-- name    : Scott1976.DataTypesAsLattices.eq_2_9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:21.133887+00:00
-- url     : https://prove2.me/theorems/07f0705e-c806-56bf-be2e-db014b3fca13
-- title:
--   Data Types As Lattices: eq 2 9
-- statement:
--   **Scott 1976, (2.9).** Application distributes over unions.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L505-L516
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L505-L516

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_2_9 (f g x : Pomega) :
    funOf (f ∪ g) x = funOf f x ∪ funOf g x := by sorry
