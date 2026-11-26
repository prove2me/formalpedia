-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_2_2_xi
-- name    : Scott1976.DataTypesAsLattices.theorem_2_2_xi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:58:46.769853+00:00
-- url     : https://prove2.me/theorems/94a6e832-7737-4ad5-9564-723fc3a573ef
-- title:
--   Data Types As Lattices: theorem 2 2 xi
-- statement:
--   **Scott 1976, Theorem 2.2 (ξ).**
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L364-L367
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Lambda.lean#L364-L367

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_2_2_xi {i : ℕ} {τ σ : Term} {ρ : ℕ → Pomega}
    (h : ∀ v, interp τ (envSet ρ i v) = interp σ (envSet ρ i v)) :
    interp (.lam i τ) ρ = interp (.lam i σ) ρ := by sorry
