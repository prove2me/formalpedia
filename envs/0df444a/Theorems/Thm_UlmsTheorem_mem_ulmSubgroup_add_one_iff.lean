-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
-- name    : UlmsTheorem.mem_ulmSubgroup_add_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:37.056077+00:00
-- url     : https://prove2.me/theorems/5b90d300-46a2-4201-9a3f-b14ee1dc1739
-- title:
--   Ulms Theorem: mem ulm Subgroup add one iff
-- statement:
--   The Ulms Theorem construction uses the mem ulm Subgroup add one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L68-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L68-L71

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

theorem UlmsTheorem.mem_ulmSubgroup_add_one_iff (α : Ordinal) (x : G) :
    x ∈ ulmSubgroup p (α + 1) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by sorry
