-- Prove2me | Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
-- name    : UlmsTheorem.ulmSubgroup_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:33.715895+00:00
-- url     : https://prove2.me/theorems/f5a8eaab-344d-45c0-aa2b-ae64a7848276
-- title:
--   Ulms Theorem: ulm Subgroup antitone
-- statement:
--   The Ulms Theorem construction uses the ulm Subgroup antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L78-L104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L78-L104

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

theorem UlmsTheorem.ulmSubgroup_antitone : Antitone (fun α ↦ ulmSubgroup p α (G := G)) := by sorry
