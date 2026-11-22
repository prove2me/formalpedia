-- Prove2me | Theorems.Thm_UlmsTheorem_pPow_succ_eq
-- name    : UlmsTheorem.pPow_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:19.420798+00:00
-- url     : https://prove2.me/theorems/109d37b4-c292-4b93-8b84-8f2f384f7021
-- title:
--   Ulms Theorem: p Pow succ eq
-- statement:
--   The Ulms Theorem construction uses the p Pow succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L57-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L57-L65

module
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Subgroups
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.pPow_succ_eq (n : ℕ) :
    (pPow p (G := G) (n + 1) : Set G) = {x | ∃ y ∈ pPow p (G := G) n, p • y = x} := by sorry
