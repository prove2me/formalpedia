-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_succ_iff
-- name    : UlmsTheorem.mem_ulmSubgroup_succ_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:41.687026+00:00
-- url     : https://prove2.me/theorems/2036331b-7743-4b57-ac16-dd15faf93172
-- title:
--   Ulms Theorem: mem ulm Subgroup succ iff
-- statement:
--   The Ulms Theorem construction uses the mem ulm Subgroup succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L63-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L63-L66

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

theorem UlmsTheorem.mem_ulmSubgroup_succ_iff (α : Ordinal) (x : G) :
    x ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      ∃ y ∈ ulmSubgroup p α (G := G), p • y = x := by sorry
