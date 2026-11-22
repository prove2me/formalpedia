-- Prove2me | Theorems.Thm_UlmsTheorem_kaplanskyMap_not_surjective_iff_proper
-- name    : UlmsTheorem.kaplanskyMap_not_surjective_iff_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:21.823837+00:00
-- url     : https://prove2.me/theorems/569f5fc4-9017-44fb-8ff5-bb4ebc8bae1a
-- title:
--   Ulms Theorem: kaplansky Map not surjective iff proper
-- statement:
--   Canonical form of Kaplansky's range lemma: his specified map is not onto
--   exactly when there is an exact-height-`α` socle element proper over `S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L421-L443
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L421-L443

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

theorem UlmsTheorem.kaplanskyMap_not_surjective_iff_proper
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    ¬ Function.Surjective (kaplanskyMap p S α) ↔
      ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
        v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
        IsProper p S v := by sorry
