-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_2
-- name    : Scott1976.DataTypesAsLattices.theorem_2_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:59:02.865693+00:00
-- url     : https://prove2.me/theorems/ca1af25a-a9ca-51df-a7dd-acda44566b3f
-- title:
--   Data Types As Lattices: theorem 2 2
-- statement:
--   **Scott 1976, Theorem 2.2 (The conversion theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L370-L372
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L370-L372

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_2 (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) := by sorry
