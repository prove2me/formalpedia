-- Prove2me | Theorems.Thm_UlmsTheorem_ulmSubgroup_succ
-- name    : UlmsTheorem.ulmSubgroup_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:35.27857+00:00
-- url     : https://prove2.me/theorems/42e16468-e81a-472f-892e-221a579b070b
-- title:
--   Ulms Theorem: ulm Subgroup succ
-- statement:
--   The Ulms Theorem construction uses the ulm Subgroup succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L49-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L49-L51

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

theorem UlmsTheorem.ulmSubgroup_succ (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) = pImage p (ulmSubgroup p α) := by sorry
