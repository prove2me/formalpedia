-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_1
-- name    : Scott1976.DataTypesAsLattices.theorem_2_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:55:12.411886+00:00
-- url     : https://prove2.me/theorems/dfccc6eb-94ae-5fd5-92f1-004ec38a78a0
-- title:
--   Data Types As Lattices: theorem 2 1
-- statement:
--   **Scott 1976, Theorem 2.1 (The continuity theorem).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L354-L356
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L354-L356

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_1 (t : Term) (ρ : ℕ → Pomega) (i : ℕ) :
    IsScottContinuous (fun v => interp t (envSet ρ i v)) := by sorry
