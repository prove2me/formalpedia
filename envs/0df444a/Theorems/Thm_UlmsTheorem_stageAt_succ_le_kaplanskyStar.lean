-- Prove2me | Theorems.Thm_UlmsTheorem_stageAt_succ_le_kaplanskyStar
-- name    : UlmsTheorem.stageAt_succ_le_kaplanskyStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:17.150449+00:00
-- url     : https://prove2.me/theorems/a4c44690-b6ee-44b4-a8a9-3aee161ba852
-- title:
--   Ulms Theorem: stage At succ le kaplansky Star
-- statement:
--   `S_{α+1}` is contained in `S_α*`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L70-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L70-L79

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
omit hp

theorem UlmsTheorem.stageAt_succ_le_kaplanskyStar (S : AddSubgroup G) (α : Ordinal) :
    stageAt p S (Order.succ α) ≤ kaplanskyStar p S α := by sorry
