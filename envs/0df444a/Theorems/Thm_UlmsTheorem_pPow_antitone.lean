-- Prove2me | Theorems.Thm_UlmsTheorem_pPow_antitone
-- name    : UlmsTheorem.pPow_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:17.652837+00:00
-- url     : https://prove2.me/theorems/c57eeb07-02e3-44e0-a3ab-e925044198d8
-- title:
--   Ulms Theorem: p Pow antitone
-- statement:
--   The Ulms Theorem construction uses the p Pow antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L54-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L54-L55

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

theorem UlmsTheorem.pPow_antitone : Antitone (fun n ↦ pPow p n (G := G)) := by sorry
