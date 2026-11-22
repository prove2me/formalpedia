-- Prove2me | Theorems.Thm_UlmsTheorem_pPow_zero_eq
-- name    : UlmsTheorem.pPow_zero_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:53:14.690878+00:00
-- url     : https://prove2.me/theorems/5c3bd326-753b-42a8-879f-2bc47931e06a
-- title:
--   Ulms Theorem: p Pow zero eq
-- statement:
--   The Ulms Theorem construction uses the p Pow zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L46-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/PGroups/Subgroups.lean#L46-L48

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

theorem UlmsTheorem.pPow_zero_eq : pPow p 0 (G := G) = ⊤ := by sorry
