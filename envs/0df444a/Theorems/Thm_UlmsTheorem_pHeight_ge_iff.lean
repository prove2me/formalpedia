-- Prove2me | Theorems.Thm_UlmsTheorem_pHeight_ge_iff
-- name    : UlmsTheorem.pHeight_ge_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:48.938659+00:00
-- url     : https://prove2.me/theorems/c11ee1f6-3266-4013-a236-5544b8eae44d
-- title:
--   Ulms Theorem: p Height ge iff
-- statement:
--   The Ulms Theorem construction uses the p Height ge iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L94-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L94-L115

module
public import Mathlib.Data.ENat.Lattice
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmSubgroups
public import Mathlib.Algebra.Module.NatInt
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
variable (p : ℕ)
variable {G : Type*} [AddCommGroup G]

theorem UlmsTheorem.pHeight_ge_iff (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ ∃ y : G, p ^ n • y = x := by sorry
