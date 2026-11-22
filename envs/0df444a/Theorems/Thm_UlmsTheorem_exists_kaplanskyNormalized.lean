-- Prove2me | Theorems.Thm_UlmsTheorem_exists_kaplanskyNormalized
-- name    : UlmsTheorem.exists_kaplanskyNormalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:47.342284+00:00
-- url     : https://prove2.me/theorems/e2121bdc-3fd3-4ef5-b5d8-7225ae0fc19f
-- title:
--   Ulms Theorem: exists kaplansky Normalized
-- statement:
--   A finite coset has a representative satisfying both of Kaplansky's
--   normalizations: first maximize the height of the representative, then, among
--   the proper representatives, maximize the height of its `p`-multiple.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1196-L1226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1196-L1226

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
omit hp

theorem UlmsTheorem.exists_kaplanskyNormalized
    {A : AddSubgroup G} (hAfinite : Set.Finite (A : Set G)) (g : G) :
    ∃ x : G,
      x - g ∈ A ∧
      IsProper p A x ∧
      ∀ y : G, y - g ∈ A → IsProper p A y →
        ulmHeight p (p • y) ≤ ulmHeight p (p • x) := by sorry
