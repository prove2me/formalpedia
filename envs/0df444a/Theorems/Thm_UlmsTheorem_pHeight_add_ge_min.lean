-- Prove2me | Theorems.Thm_UlmsTheorem_pHeight_add_ge_min
-- name    : UlmsTheorem.pHeight_add_ge_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:49.362347+00:00
-- url     : https://prove2.me/theorems/f3df6ca0-1441-49d4-a820-c8d0788e3cc5
-- title:
--   Ulms Theorem: p Height add ge min
-- statement:
--   The Ulms Theorem construction uses the p Height add ge min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L129-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L129-L148

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

theorem UlmsTheorem.pHeight_add_ge_min (x y : G) :
    min (pHeight p x) (pHeight p y) ≤ pHeight p (x + y) := by sorry
