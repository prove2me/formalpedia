-- Prove2me | Theorems.Thm_UlmsTheorem_adjoinElem_eq_sup_zmultiples
-- name    : UlmsTheorem.adjoinElem_eq_sup_zmultiples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:35.197515+00:00
-- url     : https://prove2.me/theorems/e797e94c-ef0b-4a0a-abdb-b7a04571d03b
-- title:
--   Ulms Theorem: adjoin Elem eq sup zmultiples
-- statement:
--   The Ulms Theorem construction uses the adjoin Elem eq sup zmultiples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L800-L803
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L800-L803

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

theorem UlmsTheorem.adjoinElem_eq_sup_zmultiples (A : AddSubgroup G) (g : G) :
    adjoinElem A g = A ⊔ AddSubgroup.zmultiples g := by sorry
