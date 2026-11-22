-- Prove2me | Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
-- name    : UlmsTheorem.ulmSubgroup_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:32.037452+00:00
-- url     : https://prove2.me/theorems/4565fc49-7c5f-4b32-bd75-ca0130bf09d0
-- title:
--   Ulms Theorem: ulm Subgroup zero
-- statement:
--   The Ulms Theorem construction uses the ulm Subgroup zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L42-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L42-L43

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

theorem UlmsTheorem.ulmSubgroup_zero : ulmSubgroup p (0 : Ordinal) (G := G) = ⊤ := by sorry
