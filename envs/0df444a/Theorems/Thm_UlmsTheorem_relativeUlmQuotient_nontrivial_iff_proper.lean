-- Prove2me | Theorems.Thm_UlmsTheorem_relativeUlmQuotient_nontrivial_iff_proper
-- name    : UlmsTheorem.relativeUlmQuotient_nontrivial_iff_proper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:25.111348+00:00
-- url     : https://prove2.me/theorems/42b1cbed-59ab-463f-b0e5-acb1ecb16b69
-- title:
--   Ulms Theorem: relative Ulm Quotient nontrivial iff proper
-- statement:
--   The relative Ulm quotient is nontrivial exactly when there is a proper
--   order-`p` representative of exact height `α`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L367-L417
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L367-L417

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

theorem UlmsTheorem.relativeUlmQuotient_nontrivial_iff_proper
    (S : AddSubgroup G) (α : Ordinal.{0}) :
    Nontrivial (relativeUlmQuotient p S α) ↔
      ∃ v : G, v ∈ pSocleAt p α (G := G) ∧
        v ∉ ulmSubgroup p (Order.succ α) (G := G) ∧
        IsProper p S v := by sorry
