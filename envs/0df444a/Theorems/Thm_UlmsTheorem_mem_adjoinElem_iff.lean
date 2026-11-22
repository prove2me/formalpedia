-- Prove2me | Theorems.Thm_UlmsTheorem_mem_adjoinElem_iff
-- name    : UlmsTheorem.mem_adjoinElem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:25.786832+00:00
-- url     : https://prove2.me/theorems/a696cadd-ef2c-4a1a-b4e2-806331095a96
-- title:
--   Ulms Theorem: mem adjoin Elem iff
-- statement:
--   The Ulms Theorem construction uses the mem adjoin Elem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L805-L814
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L805-L814

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

theorem UlmsTheorem.mem_adjoinElem_iff {A : AddSubgroup G} {g x : G} :
    x ∈ adjoinElem A g ↔ ∃ a ∈ A, ∃ n : ℤ, a + n • g = x := by sorry
