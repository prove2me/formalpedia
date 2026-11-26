-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_2_beta
-- name    : Scott1976.DataTypesAsLattices.theorem_2_2_beta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:56:34.475031+00:00
-- url     : https://prove2.me/theorems/98c16a77-7d8c-53ed-9664-711ff0cb6ba1
-- title:
--   Data Types As Lattices: theorem 2 2 beta
-- statement:
--   **Scott 1976, Theorem 2.2 (β).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L359-L361
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L359-L361

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_2_beta (i : ℕ) (body : Term) (ρ : ℕ → Pomega) (y : Pomega) :
    funOf (interp (.lam i body) ρ) y = interp body (envSet ρ i y) := by sorry
