-- Prove2me | Theorems.Thm_UlmsTheorem_pPow_succ_le
-- name    : UlmsTheorem.pPow_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:16.380868+00:00
-- url     : https://prove2.me/theorems/896e08b0-1c68-4271-8e0d-d6b4a80d5410
-- title:
--   Ulms Theorem: p Pow succ le
-- statement:
--   The Ulms Theorem construction uses the p Pow succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L50-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L50-L52

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

theorem UlmsTheorem.pPow_succ_le (n : ℕ) : pPow p (n + 1) ≤ pPow p (G := G) n := by sorry
