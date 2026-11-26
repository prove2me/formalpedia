-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_7_2_i
-- name    : Scott1976.DataTypesAsLattices.theorem_7_2_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:03:56.497796+00:00
-- url     : https://prove2.me/theorems/5cca0d6c-6efc-5dcc-8da9-c08ff999bb3e
-- title:
--   Data Types As Lattices: theorem 7 2 i
-- statement:
--   **Scott 1976, Theorem 7.2 (i).** `E_a` is the identity on the range of `a`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L124-L126
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Functionality.lean#L124-L126

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_7_2_i (a x y : Pomega) :
    (Ea a).rel x y ↔ typed x a ∧ typed y a ∧ x = y := by sorry
