-- Prove2me | Theorems.Thm_UlmsTheorem_ulmSubgroup_limit
-- name    : UlmsTheorem.ulmSubgroup_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:38.073443+00:00
-- url     : https://prove2.me/theorems/58006dc8-f2b7-438d-932f-8d8b5e613709
-- title:
--   Ulms Theorem: ulm Subgroup limit
-- statement:
--   The Ulms Theorem construction uses the ulm Subgroup limit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L53-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L53-L61

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

theorem UlmsTheorem.ulmSubgroup_limit (o : Ordinal) (ho : Order.IsSuccLimit o) :
    ulmSubgroup p o (G := G) = ⨅ (β : Ordinal) (_ : β < o), ulmSubgroup p β := by sorry
