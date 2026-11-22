-- Prove2me | Theorems.Thm_UlmsTheorem_dvd_of_zsmul_mem_of_not_mem
-- name    : UlmsTheorem.dvd_of_zsmul_mem_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:22.950468+00:00
-- url     : https://prove2.me/theorems/3ce96b2e-b7af-4117-b846-ea66d27cc47d
-- title:
--   Ulms Theorem: dvd of zsmul mem of not mem
-- statement:
--   The Ulms Theorem construction uses the dvd of zsmul mem of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L816-L847
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L816-L847

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

theorem UlmsTheorem.dvd_of_zsmul_mem_of_not_mem
    {A : AddSubgroup G} {g : G}
    (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    (k : ℤ) (hk : k • g ∈ A) : (↑p : ℤ) ∣ k := by sorry
