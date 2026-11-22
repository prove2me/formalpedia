-- Prove2me | Theorems.Thm_UlmsTheorem_proper_adjoin_rep_mem_iff
-- name    : UlmsTheorem.proper_adjoin_rep_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:47.982572+00:00
-- url     : https://prove2.me/theorems/76592834-b022-4062-870d-8225d61e4262
-- title:
--   Ulms Theorem: proper adjoin rep mem iff
-- statement:
--   The elementwise filtration calculation behind the one-generator
--   extension.  If `x` and `w` have the same exact height, are proper over the
--   matched subgroups, and satisfy the same `p`-relation, then corresponding
--   normal forms `a + n • x` and `φ(a) + n • w` lie in exactly the same Ulm
--   subgroups.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1043-L1086
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1043-L1086

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

theorem UlmsTheorem.proper_adjoin_rep_mem_iff
    {A : AddSubgroup G} {B : AddSubgroup H}
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {x : G} {w : H} {α β : Ordinal.{0}}
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p A x) (hwProper : IsProper p B w)
    (hpxA : p • x ∈ A)
    (hpw : p • w = (φ ⟨p • x, hpxA⟩ : H))
    (a : A) (n : ℤ) :
    ((a : G) + n • x ∈ ulmSubgroup p β (G := G)) ↔
      ((φ a : H) + n • w ∈ ulmSubgroup p β (G := H)) := by sorry
