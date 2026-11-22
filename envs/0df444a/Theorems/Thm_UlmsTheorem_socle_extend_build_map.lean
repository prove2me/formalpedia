-- Prove2me | Theorems.Thm_UlmsTheorem_socle_extend_build_map
-- name    : UlmsTheorem.socle_extend_build_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:35.785966+00:00
-- url     : https://prove2.me/theorems/21b85f01-33d9-4160-9003-dcb0d95517df
-- title:
--   Ulms Theorem: socle extend build map
-- statement:
--   The Ulms Theorem construction uses the socle extend build map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L849-L914
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L849-L914

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

theorem UlmsTheorem.socle_extend_build_map
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) {h : H}
    (hpg_in : p • g ∈ A)
    (hrel : p • h = (φ ⟨p • g, hpg_in⟩ : H)) :
    ∃ φ' : adjoinElem A g →+ (⊤ : AddSubgroup H),
      (∀ a : A, (φ' ⟨a, le_adjoinElem (A := A) (g := g) a.prop⟩ : H) = φ a) ∧
      (φ' ⟨g, mem_adjoinElem_right (A := A) g⟩ : H) = h := by sorry
