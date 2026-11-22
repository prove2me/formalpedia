-- Prove2me | Theorems.Thm_UlmsTheorem_kaplanskyMap_range
-- name    : UlmsTheorem.kaplanskyMap_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:25.239058+00:00
-- url     : https://prove2.me/theorems/dab8d5db-6707-444d-a7d0-506a6dc46f8d
-- title:
--   Ulms Theorem: kaplansky Map range
-- statement:
--   The canonical Kaplansky map occupies exactly
--   `((S + G_(α+1)) ∩ P_α) / P_(α+1)` in the ordinary Ulm layer.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L303-L363
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L303-L363

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

theorem UlmsTheorem.kaplanskyMap_range
    (S : AddSubgroup G) (α : Ordinal) :
    LinearMap.range (kaplanskyLinearMap p S α (kaplanskyMap p S α)) =
      relativeOccupiedSubmodule p S α := by sorry
