-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_range_lemma
-- name    : UlmsTheorem.kaplansky_range_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:23.924661+00:00
-- url     : https://prove2.me/theorems/7229e7f6-748a-47c5-bbe4-d73591d224de
-- title:
--   Ulms Theorem: kaplansky range lemma
-- statement:
--   Kaplansky's range lemma, the central relative ingredient in the one-generator
--   extension argument.  The map sends a class represented by `x ∈ S_α*` to the class of
--   `x-y` in `P_α/P_{α+1}`, where `py = px` and `y ∈ G_{α+1}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L448-L457
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L448-L457

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

theorem UlmsTheorem.kaplansky_range_lemma (S : AddSubgroup G) (α : Ordinal.{0}) :
    ∃ U : kaplanskyDomainQuotient p S α →+
        ulmQuotient p α (G := G),
      Function.Injective U ∧
      (¬ Function.Surjective U ↔
        ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
          v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
          IsProper p S v) := by sorry
