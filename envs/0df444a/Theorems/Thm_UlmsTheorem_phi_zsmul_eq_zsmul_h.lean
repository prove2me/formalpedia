-- Prove2me | Theorems.Thm_UlmsTheorem_phi_zsmul_eq_zsmul_h
-- name    : UlmsTheorem.phi_zsmul_eq_zsmul_h
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:37.416089+00:00
-- url     : https://prove2.me/theorems/f4c204dc-f3b0-4d8b-ad85-d4a1373c4f1c
-- title:
--   Ulms Theorem: phi zsmul eq zsmul h
-- statement:
--   The Ulms Theorem construction uses the phi zsmul eq zsmul h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L916-L940
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L916-L940

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

theorem UlmsTheorem.phi_zsmul_eq_zsmul_h
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    (k : ℤ) (hk : k • g ∈ A) :
    (↑(φ ⟨k • g, hk⟩) : H) = k • h := by sorry
