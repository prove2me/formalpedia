-- Prove2me | Theorems.Thm_UlmsTheorem_socle_extend_build_map_heightPres
-- name    : UlmsTheorem.socle_extend_build_map_heightPres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:46.2769+00:00
-- url     : https://prove2.me/theorems/383b7778-9dda-4f80-8663-6a06120c6c32
-- title:
--   Ulms Theorem: socle extend build map height Pres
-- statement:
--   The quotient-built homomorphism on `A + ⟨x⟩` is height-preserving once
--   the chosen image `w` satisfies Kaplansky's exact-height and properness
--   conditions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1091-L1137
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1091-L1137

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

theorem UlmsTheorem.socle_extend_build_map_heightPres
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {x : G} (hx_notin : x ∉ A) {w : H} {α : Ordinal.{0}}
    (hpxA : p • x ∈ A)
    (hpw : p • w = (φ ⟨p • x, hpxA⟩ : H))
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p A x) (hwProper : IsProper p B w) :
    ∃ φ' : adjoinElem A x →+ (⊤ : AddSubgroup H),
      (∀ a : A,
        (φ' ⟨a, le_adjoinElem (A := A) (g := x) a.prop⟩ : H) = φ a) ∧
      (φ' ⟨x, mem_adjoinElem_right (A := A) x⟩ : H) = w ∧
      IsHeightPresOn p φ' := by sorry
