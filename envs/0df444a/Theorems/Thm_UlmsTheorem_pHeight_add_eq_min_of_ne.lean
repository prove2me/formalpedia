-- Prove2me | Theorems.Thm_UlmsTheorem_pHeight_add_eq_min_of_ne
-- name    : UlmsTheorem.pHeight_add_eq_min_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:58.726309+00:00
-- url     : https://prove2.me/theorems/01cd55f7-3898-4544-9d0a-bc7c3b36231b
-- title:
--   Ulms Theorem: p Height add eq min of ne
-- statement:
--   The Ulms Theorem construction uses the p Height add eq min of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L150-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L150-L173

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

theorem UlmsTheorem.pHeight_add_eq_min_of_ne (x y : G) (h : pHeight p x ≠ pHeight p y) :
    pHeight p (x + y) = min (pHeight p x) (pHeight p y) := by sorry
