-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_1_complete
-- name    : Scott1976.DataTypesAsLattices.theorem_4_1_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:57:01.08149+00:00
-- url     : https://prove2.me/theorems/809d586f-c7a5-5ca0-9f5d-b80fe1a8ac25
-- title:
--   Data Types As Lattices: theorem 4 1 complete
-- statement:
--   **Scott 1976, Theorem 4.1 (The lattice theorem), complete-lattice half.**
--   Fixed points of a continuous map are closed under arbitrary infima
--   `x ↦ fix(z ↦ f(z) ∩ ⋂ A)`.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L156-L171
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L156-L171

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_1_complete (f : Pomega → Pomega) (hf : IsScottContinuous f)
    (A : Set Pomega) (_hA : A ⊆ Fixpoints f) :
    gfpBelow f (⋂₀ A) ∈ Fixpoints (fun z => f z ∩ ⋂₀ A) := by sorry
