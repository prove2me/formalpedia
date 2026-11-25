-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_analyticAt_of_sections_46f0407d8b3a
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_analyticAt_of_sections_46f0407d8b3a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:43.009047+00:00
-- url     : https://prove2.me/theorems/5c71dd9c-4bce-465c-9665-801aca914b9e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic analytic At of sections 46f0407d8b3a: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic analytic At of sections 46f0407d8b3a construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Fibre Discriminant Holomorphic analytic At of sections 46f0407d8b3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreDiscriminantHolomorphic.lean#L249-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreDiscriminantHolomorphic.lean#L249-L297

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic
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
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_analyticAt_of_sections_46f0407d8b3a {Y : Set (σ → ℂ)} {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)}
    {D : Set (Fin d → ℂ)} {N : ℕ} (l : (σ → ℂ) →L[ℂ] ℂ) (hD : IsOpen D)
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) {y₀ : Fin d → ℂ} (hy₀ : y₀ ∈ D)
    (hN : {x | x ∈ Y ∧ A x = y₀}.encard = N)
    (hsec : ∀ x ∈ Y, A x = y₀ → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧ Y ∩ V = h '' O) :
    AnalyticAt ℂ (fibreDiscr Y A l N) y₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«FibreDiscriminantHolomorphic».«analyticAt_of_sections» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_analyticAt_of_sections_46f0407d8b3a
