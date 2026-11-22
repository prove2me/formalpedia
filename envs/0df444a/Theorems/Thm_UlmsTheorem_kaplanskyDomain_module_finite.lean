-- Prove2me | Theorems.Thm_UlmsTheorem_kaplanskyDomain_module_finite
-- name    : UlmsTheorem.kaplanskyDomain_module_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:20.90706+00:00
-- url     : https://prove2.me/theorems/200b9393-c59e-48a7-bfdb-b58535e80929
-- title:
--   Ulms Theorem: kaplansky Domain module finite
-- statement:
--   Kaplansky's source quotient is finite-dimensional when the stage itself
--   is finite.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L646-L662
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L646-L662

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

theorem UlmsTheorem.kaplanskyDomain_module_finite
    (S : AddSubgroup G) (hSfinite : Set.Finite (S : Set G))
    (α : Ordinal.{0}) :
    Module.Finite (ZMod p) (kaplanskyDomainQuotient p S α) := by sorry
