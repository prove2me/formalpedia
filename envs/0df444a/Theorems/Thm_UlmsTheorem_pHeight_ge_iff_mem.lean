-- Prove2me | Theorems.Thm_UlmsTheorem_pHeight_ge_iff_mem
-- name    : UlmsTheorem.pHeight_ge_iff_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:59.09318+00:00
-- url     : https://prove2.me/theorems/687ac83e-746b-4fb5-b76a-f85af13e7e3c
-- title:
--   Ulms Theorem: p Height ge iff mem
-- statement:
--   The Ulms Theorem construction uses the p Height ge iff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L117-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Heights.lean#L117-L119

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

theorem UlmsTheorem.pHeight_ge_iff_mem (x : G) (n : ℕ) :
    (n : ℕ∞) ≤ pHeight p x ↔ x ∈ pPow p n := by sorry
