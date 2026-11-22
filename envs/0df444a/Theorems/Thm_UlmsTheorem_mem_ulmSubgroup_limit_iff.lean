-- Prove2me | Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_limit_iff
-- name    : UlmsTheorem.mem_ulmSubgroup_limit_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:39.560534+00:00
-- url     : https://prove2.me/theorems/99b52ee3-4ab3-4757-bbb9-b0aacece6bd3
-- title:
--   Ulms Theorem: mem ulm Subgroup limit iff
-- statement:
--   The Ulms Theorem construction uses the mem ulm Subgroup limit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L73-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L73-L76

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

theorem UlmsTheorem.mem_ulmSubgroup_limit_iff {o : Ordinal} (ho : Order.IsSuccLimit o) (x : G) :
    x ∈ ulmSubgroup p o (G := G) ↔ ∀ β < o, x ∈ ulmSubgroup p β := by sorry
