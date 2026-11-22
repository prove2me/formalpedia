-- Prove2me | Theorems.Thm_UlmsTheorem_map_ulmSubgroup_le
-- name    : UlmsTheorem.map_ulmSubgroup_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:38.924438+00:00
-- url     : https://prove2.me/theorems/8f005361-3872-4c3d-a3ea-7ba9314325a4
-- title:
--   Ulms Theorem: map ulm Subgroup le
-- statement:
--   The Ulms Theorem construction uses the map ulm Subgroup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L142-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L142-L159

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

theorem UlmsTheorem.map_ulmSubgroup_le {H : Type*} [AddCommGroup H] (φ : G →+ H) (α : Ordinal) :
    (ulmSubgroup p α (G := G)).map φ ≤ ulmSubgroup p α (G := H) := by sorry
