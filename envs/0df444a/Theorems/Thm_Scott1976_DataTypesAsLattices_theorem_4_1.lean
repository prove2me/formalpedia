-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_4_1
-- name    : Scott1976.DataTypesAsLattices.theorem_4_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:00:33.572443+00:00
-- url     : https://prove2.me/theorems/c08e114e-825e-46f9-83ec-f3ff08c8b7c2
-- title:
--   Data Types As Lattices: theorem 4 1
-- statement:
--   **Scott 1976, Theorem 4.1.** Fixed points of a continuous function form
--   a complete lattice; those of a retract are the range of that retract.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L175-L185
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Retracts.lean#L175-L185

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints (fun z => f z ∩ ⋂₀ A)) ∧
      ∀ {a} (_ha : IsRetract a),
        Fixpoints (funOf a) = {x | typed x a} := by sorry
