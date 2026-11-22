-- Prove2me | Theorems.Thm_UlmsTheorem_exists_kaplanskyTarget_caseII
-- name    : UlmsTheorem.exists_kaplanskyTarget_caseII
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:49.839497+00:00
-- url     : https://prove2.me/theorems/29d02c8c-aabe-4d2c-8923-21292e9718c6
-- title:
--   Ulms Theorem: exists kaplansky Target case II
-- statement:
--   Kaplansky's Case II target construction.
--
--   When `p • x` lies two levels higher, subtract a higher root to expose a
--   proper exact-height socle element.  The canonical range lemma and equality of
--   the ordinary Ulm invariant transfer the resulting room to the target side;
--   adding that target socle element to a higher root gives the required image.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1310-L1365
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1310-L1365

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

theorem UlmsTheorem.exists_kaplanskyTarget_caseII
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α)
    {x : G}
    (hinv :
      ulmInvariant p α (G := G) = ulmInvariant p α (G := H))
    (hpxA : p • x ∈ s.A)
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hxProper : IsProper p s.A x)
    (hcaseII :
      p • x ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G)) :
    ∃ w : H,
      p • w = (s.e ⟨p • x, hpxA⟩ : H) ∧
      w ∈ ulmSubgroup p α (G := H) ∧
      w ∉ ulmSubgroup p (Order.succ α) (G := H) ∧
      IsProper p s.B w := by sorry
