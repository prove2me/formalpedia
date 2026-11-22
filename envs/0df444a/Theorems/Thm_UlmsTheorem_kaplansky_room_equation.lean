-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_room_equation
-- name    : UlmsTheorem.kaplansky_room_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:17.861496+00:00
-- url     : https://prove2.me/theorems/767ca84b-487a-44e3-8444-2fd7ef50529d
-- title:
--   Ulms Theorem: kaplansky room equation
-- statement:
--   Rank bookkeeping for Kaplansky's map:
--   `room + occupied = the ordinary Ulm invariant`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L149-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L149-L155

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

theorem UlmsTheorem.kaplansky_room_equation
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    kaplanskyRoomInvariant p S α U +
        Module.rank (ZMod p) (kaplanskyOccupiedSubmodule p S α U) =
      ulmInvariant p α (G := G) := by sorry
