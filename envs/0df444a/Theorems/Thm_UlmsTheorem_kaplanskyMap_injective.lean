-- Prove2me | Theorems.Thm_UlmsTheorem_kaplanskyMap_injective
-- name    : UlmsTheorem.kaplanskyMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:23.595317+00:00
-- url     : https://prove2.me/theorems/5c2eab6e-e424-47a6-82a2-944a047a89b0
-- title:
--   Ulms Theorem: kaplansky Map injective
-- statement:
--   The Ulms Theorem construction uses the kaplansky Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L269-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L269-L299

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

theorem UlmsTheorem.kaplanskyMap_injective
    (S : AddSubgroup G) (α : Ordinal) :
    Function.Injective (kaplanskyMap p S α) := by sorry
