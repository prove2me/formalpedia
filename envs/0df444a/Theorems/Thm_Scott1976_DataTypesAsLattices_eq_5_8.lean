-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_eq_5_8
-- name    : Scott1976.DataTypesAsLattices.eq_5_8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:01:36.346195+00:00
-- url     : https://prove2.me/theorems/7a65a37f-d8f9-4f3b-b590-d2f3ac811583
-- title:
--   Data Types As Lattices: eq 5 8
-- statement:
--   **Scott 1976, (5.8).** `u = [[u]₀, [u]₁]`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L40-L54
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Closures.lean#L40-L54

import Mathlib.Algebra.Ring.Parity
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Closures
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.eq_5_8 (u : Pomega) : squarePair (squareFst u) (squareSnd u) = u := by sorry
