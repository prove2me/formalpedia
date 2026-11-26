-- Prove2me | Theorems.Thm_Scott1976_DataTypesAsLattices_pair_inj
-- name    : Scott1976.DataTypesAsLattices.pair_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:53:08.195648+00:00
-- url     : https://prove2.me/theorems/a6c5e4a8-e474-4efa-954d-698371d57746
-- title:
--   Data Types As Lattices: pair inj
-- statement:
--   The Data Types As Lattices construction uses the pair inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L134-L164
-- source:
--   https://github.com/catskillsresearch/scott1976/blob/2081973122a631d34dc74f83cfc3f7495991415b/Scott1976/DataTypesAsLattices/Pomega.lean#L134-L164

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices

theorem Scott1976.DataTypesAsLattices.pair_inj {n₁ m₁ n₂ m₂ : ℕ} (h : pair n₁ m₁ = pair n₂ m₂) :
    n₁ = n₂ ∧ m₁ = m₂ := by sorry
