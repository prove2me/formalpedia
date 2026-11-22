-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_extend
-- name    : UlmsTheorem.kaplansky_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:59.423104+00:00
-- url     : https://prove2.me/theorems/b38b027a-0d74-41db-a0be-dfed5bf03151
-- title:
--   Ulms Theorem: kaplansky extend
-- statement:
--   Kaplansky's finite-stage extension theorem.
--
--   Starting from finite subgroups related by a height-preserving isomorphism, extend the
--   stage to cover a prescribed source element.  This is the iterated conclusion used by
--   the back-and-forth construction, not the single `px ∈ A` step on page 30: primaryness
--   first supplies a power of `p` lying in `A`, and the proof then applies the single-step
--   construction repeatedly.  Only the source group must be reduced in this direction;
--   the target reducedness hypothesis enters when this theorem is applied symmetrically
--   for the back step.  At each single step `exists_kaplanskyNormalized` supplies
--   Kaplansky's two normalizations, and Case II uses the canonical range theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1474-L1514
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1474-L1514

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

theorem UlmsTheorem.kaplansky_extend
    (hG : IsReducedPGroup p G)
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : UlmStage p (G := G) (H := H)) (g : G) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by sorry
