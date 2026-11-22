-- Prove2me | Theorems.Thm_UlmsTheorem_ulmSubgroup_add_one
-- name    : UlmsTheorem.ulmSubgroup_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:37.554536+00:00
-- url     : https://prove2.me/theorems/a8931bac-976a-44bf-9629-a80c8146ab83
-- title:
--   Ulms Theorem: ulm Subgroup add one
-- statement:
--   The Ulms Theorem construction uses the ulm Subgroup add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L45-L47
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L45-L47

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

theorem UlmsTheorem.ulmSubgroup_add_one (α : Ordinal) :
    ulmSubgroup p (α + 1) (G := G) = pImage p (ulmSubgroup p α) := by sorry
