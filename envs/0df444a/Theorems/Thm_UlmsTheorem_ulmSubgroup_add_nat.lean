-- Prove2me | Theorems.Thm_UlmsTheorem_ulmSubgroup_add_nat
-- name    : UlmsTheorem.ulmSubgroup_add_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:42.876035+00:00
-- url     : https://prove2.me/theorems/869cd9ae-1fce-4651-9410-f9a71ab6bbcf
-- title:
--   Ulms Theorem: ulm Subgroup add nat
-- statement:
--   The Ulms Theorem construction uses the ulm Subgroup add nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L136-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L136-L140

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

theorem UlmsTheorem.ulmSubgroup_add_nat (α : Ordinal) (n : ℕ) :
    ulmSubgroup p (α + n) (G := G) =
      { x | ∃ y ∈ ulmSubgroup p α (G := G), p ^ n • y = x } := by sorry
