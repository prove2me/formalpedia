-- Prove2me | Theorems.Thm_UlmsTheorem_pHeight_add_ge
-- name    : UlmsTheorem.pHeight_add_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:51.503248+00:00
-- url     : https://prove2.me/theorems/2b5f311b-345f-4966-a0b6-11d4d2491fe9
-- title:
--   Ulms Theorem: p Height add ge
-- statement:
--   The Ulms Theorem construction uses the p Height add ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L121-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L121-L127

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

theorem UlmsTheorem.pHeight_add_ge (x y : G) (n : ℕ)
    (hx : (n : ℕ∞) ≤ pHeight p x) (hy : (n : ℕ∞) ≤ pHeight p y) :
    (n : ℕ∞) ≤ pHeight p (x + y) := by sorry
