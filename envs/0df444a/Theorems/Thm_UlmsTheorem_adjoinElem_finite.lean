-- Prove2me | Theorems.Thm_UlmsTheorem_adjoinElem_finite
-- name    : UlmsTheorem.adjoinElem_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:31.31458+00:00
-- url     : https://prove2.me/theorems/c7cd1de4-afa6-4897-b796-df83ec8402ea
-- title:
--   Ulms Theorem: adjoin Elem finite
-- statement:
--   Adjoining one element to a finite subgroup of a primary group remains finite.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L774-L798
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L774-L798

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

theorem UlmsTheorem.adjoinElem_finite
    (hG : IsPrimaryPGroup p G)
    {A : AddSubgroup G} (hAfinite : Set.Finite (A : Set G)) (g : G) :
    Set.Finite (adjoinElem A g : Set G) := by sorry
