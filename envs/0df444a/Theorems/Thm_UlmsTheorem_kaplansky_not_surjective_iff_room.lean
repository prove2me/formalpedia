-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_not_surjective_iff_room
-- name    : UlmsTheorem.kaplansky_not_surjective_iff_room
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:18.835075+00:00
-- url     : https://prove2.me/theorems/438e4b3e-deab-44f3-830b-bceb89a79374
-- title:
--   Ulms Theorem: kaplansky not surjective iff room
-- statement:
--   “Not onto means room”: a Kaplansky map fails to be surjective exactly when
--   its room quotient is nontrivial.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L159-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L159-L167

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

theorem UlmsTheorem.kaplansky_not_surjective_iff_room
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    ¬ Function.Surjective U ↔ Nontrivial (kaplanskyRoomQuotient p S α U) := by sorry
