-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_nat_iff
-- name    : UlmsTheorem.mem_ulmSubgroup_add_nat_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:36.944225+00:00
-- url     : https://prove2.me/theorems/71b45292-9e18-4355-9547-4c776acb10fb
-- title:
--   Ulms Theorem: mem ulm Subgroup add nat iff
-- statement:
--   The Ulms Theorem construction uses the mem ulm Subgroup add nat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L118-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L118-L134

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

theorem UlmsTheorem.mem_ulmSubgroup_add_nat_iff (α : Ordinal) (n : ℕ) (x : G) :
    x ∈ ulmSubgroup p (α + n) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x := by sorry
