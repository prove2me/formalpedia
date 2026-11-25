-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_coeffs_extend_fb862d39adb5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_coeffs_extend_fb862d39adb5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:45.352521+00:00
-- url     : https://prove2.me/theorems/aa948f80-3d4b-4e4e-8b3c-972c8b9d477d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fibre coeffs extend fb862d39adb5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fibre
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fibre coeffs extend fb862d39adb5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets fibre coeffs extend fb862d39adb5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L80-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L80-L154

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_coeffs_extend_fb862d39adb5 {σ : Type} [Fintype σ] {k m : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (D : Set (Fin k → ℂ)) (δ g : (Fin k → ℂ) → ℂ) (φ : (σ → ℂ) → ℂ) (M : ℝ)
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D)
    (hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hgδ : ∀ y ∈ D, g y ≠ 0 → δ y ≠ 0)
    (hsheets : ∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ Z ∩ W, A z = y' → z ∈ Set.range (fun j => s j y'))
    (hφ : HolomorphicOnSubset φ {x | x ∈ Z ∩ W ∧ A x ∈ D ∧ g (A x) ≠ 0})
    (hM : ∀ x ∈ Z ∩ W, A x ∈ D → g (A x) ≠ 0 → ‖φ x‖ ≤ M) :
    ∃ c : Fin m → (Fin k → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (c j) D) ∧
      ∀ y ∈ D, g y ≠ 0 → ∀ s : Fin m → σ → ℂ, (∀ j, s j ∈ Z ∩ W ∧ A (s j) = y) →
        Function.Injective s → (∀ z ∈ Z ∩ W, A z = y → z ∈ Set.range s) →
        ∀ t : ℂ, t ^ m + ∑ j, c j y * t ^ (j : ℕ) = ∏ j, (t - φ (s j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«fibre_coeffs_extend» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_coeffs_extend_fb862d39adb5
