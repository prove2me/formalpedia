-- Prove2me | Theorems.Thm_UlmsTheorem_extend_by_one_of_mem
-- name    : UlmsTheorem.extend_by_one_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:34.258801+00:00
-- url     : https://prove2.me/theorems/ad4a1232-e8b2-4232-a61e-635e102bdec2
-- title:
--   Ulms Theorem: extend by one of mem
-- statement:
--   Trivial extension when the prescribed generator is already in the domain subgroup.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L722-L734
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L722-L734

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

theorem UlmsTheorem.extend_by_one_of_mem
    {A : AddSubgroup G}
    {B : AddSubgroup H} (hB : IsPure p B)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by sorry
