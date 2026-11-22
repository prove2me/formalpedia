-- Prove2me | Theorems.Thm_UlmsTheorem_mem_pImage
-- name    : UlmsTheorem.mem_pImage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:15.515667+00:00
-- url     : https://prove2.me/theorems/f867a05b-d721-4621-9a16-0d14c18ae021
-- title:
--   Ulms Theorem: mem p Image
-- statement:
--   The Ulms Theorem construction uses the mem p Image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L86-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L86-L87

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

theorem UlmsTheorem.mem_pImage (H : AddSubgroup G) (x : G) :
    x ∈ pImage p H ↔ ∃ y ∈ H, p • y = x := by sorry
