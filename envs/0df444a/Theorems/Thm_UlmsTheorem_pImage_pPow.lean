-- Prove2me | Theorems.Thm_UlmsTheorem_pImage_pPow
-- name    : UlmsTheorem.pImage_pPow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:16.605801+00:00
-- url     : https://prove2.me/theorems/99545edc-e75e-4df7-b0ae-66f8fa30d46c
-- title:
--   Ulms Theorem: p Image p Pow
-- statement:
--   The Ulms Theorem construction uses the p Image p Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L89-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L89-L97

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

theorem UlmsTheorem.pImage_pPow (n : ℕ) :
    pImage p (pPow p n (G := G)) = pPow p (n + 1) := by sorry
