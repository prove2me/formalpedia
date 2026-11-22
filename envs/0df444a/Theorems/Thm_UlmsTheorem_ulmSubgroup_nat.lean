-- Prove2me | Theorems.Thm_UlmsTheorem_ulmSubgroup_nat
-- name    : UlmsTheorem.ulmSubgroup_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:35.068555+00:00
-- url     : https://prove2.me/theorems/c9d384ca-4a93-4a22-a974-a58ce582be6c
-- title:
--   Ulms Theorem: ulm Subgroup nat
-- statement:
--   The Ulms Theorem construction uses the ulm Subgroup nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L106-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/UlmSubgroups.lean#L106-L112

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

theorem UlmsTheorem.ulmSubgroup_nat (n : ℕ) : ulmSubgroup p (n : Ordinal) (G := G) = pPow p n := by sorry
