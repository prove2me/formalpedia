-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_extend_one_of_target
-- name    : UlmsTheorem.kaplansky_extend_one_of_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:46.136373+00:00
-- url     : https://prove2.me/theorems/702d7a2f-a9d6-4269-b685-a5b8e73f87b2
-- title:
--   Ulms Theorem: kaplansky extend one of target
-- statement:
--   Once the target representative required on page 30 has been found, the
--   actual finite-stage extension is formal algebra: build the quotient map,
--   restrict its codomain to its range, and use height preservation for
--   injectivity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1143-L1190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1143-L1190

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

theorem UlmsTheorem.kaplansky_extend_one_of_target
    (hG : IsReducedPGroup p G)
    (s : UlmStage p (G := G) (H := H))
    {x : G} (hx_notin : x ∉ s.A) {w : H} {α : Ordinal.{0}}
    (hpxA : p • x ∈ s.A)
    (hpw : p • w = (s.e ⟨p • x, hpxA⟩ : H))
    (hxα : x ∈ ulmSubgroup p α (G := G))
    (hxSucc : x ∉ ulmSubgroup p (Order.succ α) (G := G))
    (hwα : w ∈ ulmSubgroup p α (G := H))
    (hwSucc : w ∉ ulmSubgroup p (Order.succ α) (G := H))
    (hxProper : IsProper p s.A x) (hwProper : IsProper p s.B w) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      x ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by sorry
