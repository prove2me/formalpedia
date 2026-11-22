-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_nat_iff
-- name    : UlmsTheorem.mem_ulmSubgroup_nat_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:43.650321+00:00
-- url     : https://prove2.me/theorems/56591773-5171-4b77-ab79-3e56df603332
-- title:
--   Ulms Theorem: mem ulm Subgroup nat iff
-- statement:
--   The Ulms Theorem construction uses the mem ulm Subgroup nat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L114-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L114-L116

module
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.mem_ulmSubgroup_nat_iff (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (n : Ordinal) (G := G) ↔ ∃ y : G, p ^ n • y = x := by sorry
