-- Prove2me | Theorems.Thm_UlmsTheorem_kaplansky_extend_one
-- name    : UlmsTheorem.kaplansky_extend_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:57:53.991139+00:00
-- url     : https://prove2.me/theorems/45017252-1d8c-459f-922e-1437be071b06
-- title:
--   Ulms Theorem: kaplansky extend one
-- statement:
--   Kaplansky's page-30 one-step extension.
--
--   The input condition `p • g ∈ A` is the precise one-step hypothesis.  A
--   normalized representative of the coset `g + A` has an attained exact height;
--   the two target-selection lemmas above then cover whether its `p`-multiple has
--   height exactly one higher or lies at least two levels higher.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1414-L1462
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean#L1414-L1462

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

theorem UlmsTheorem.kaplansky_extend_one
    (hG : IsReducedPGroup p G)
    (hinv : ∀ β : Ordinal.{0},
      ulmInvariant p β (G := G) = ulmInvariant p β (G := H))
    (s : UlmStage p (G := G) (H := H)) (g : G)
    (hpgA : p • g ∈ s.A) :
    ∃ (s' : UlmStage p (G := G) (H := H))
      (hAA : s.A ≤ s'.A) (_hBB : s.B ≤ s'.B),
      g ∈ s'.A ∧
      ∀ a : s.A, (s'.e ⟨a, hAA a.prop⟩ : H) = s.e a := by sorry
