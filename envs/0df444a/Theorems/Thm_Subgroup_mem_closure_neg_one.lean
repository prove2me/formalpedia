-- Prove2me | Theorems.Thm_Subgroup_mem_closure_neg_one
-- name    : Subgroup.mem_closure_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:50.015343+00:00
-- url     : https://prove2.me/theorems/63712fc2-091e-475d-ab9e-bc8e1d43a760
-- title:
--   Subgroup: mem closure neg one
-- statement:
--   The Subgroup construction uses the mem closure neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Group/Subgroup/Lattice.lean#L5-L15
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Mathlib/Algebra/Group/Subgroup/Lattice.lean#L5-L15

import Mathlib.Algebra.Group.Subgroup.Lattice
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
set_option autoImplicit false

theorem Subgroup.mem_closure_neg_one {α : Type*} [Group α] [HasDistribNeg α] {a : α} :
    a ∈ Subgroup.closure {-1} ↔ a = 1 ∨ a = -1 := by sorry
