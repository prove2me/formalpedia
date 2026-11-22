-- Prove2me | Theorems.Thm_UlmsTheorem_extend_well_defined
-- name    : UlmsTheorem.extend_well_defined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:58:40.689163+00:00
-- url     : https://prove2.me/theorems/c4260445-0152-4793-8633-13143ecd3fbb
-- title:
--   Ulms Theorem: extend well defined
-- statement:
--   The Ulms Theorem construction uses the extend well defined property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L942-L986
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L942-L986

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

theorem UlmsTheorem.extend_well_defined
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B)
    {g : G} (hg_notin : g ∉ A) (hpg_in : p • g ∈ A)
    {h : H} (hh_eq : p • h = (↑(φ ⟨p • g, hpg_in⟩) : H))
    {a₁ a₂ : G} {n₁ n₂ : ℤ} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (heq : a₁ + n₁ • g = a₂ + n₂ • g) :
    (↑(φ ⟨a₁, ha₁⟩) : H) + n₁ • h = (↑(φ ⟨a₂, ha₂⟩) : H) + n₂ • h := by sorry
