-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_2_11
-- name    : Scott1976.DataTypesAsLattices.eq_2_11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:33.09748+00:00
-- url     : https://prove2.me/theorems/06e89505-11a5-53a5-b6b4-283df27f86f4
-- title:
--   Data Types As Lattices: eq 2 11
-- statement:
--   **Scott 1976, (2.11).** One inclusion; equality needs both arguments to be graphs.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L519-L522
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L519-L522

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_2_11 (f g x : Pomega) :
    funOf (f ∩ g) x ⊆ funOf f x ∩ funOf g x := by sorry
