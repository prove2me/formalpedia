-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_local_extension_09ab203d386c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_local_extension_09ab203d386c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:12.364683+00:00
-- url     : https://prove2.me/theorems/d0b71beb-2e93-4006-a46a-caca46c12918
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic local extension 09ab203d386c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic local extension 09ab203d386c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic local extension 09ab203d386c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRiemannExtensionAnalytic.lean#L123-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRiemannExtensionAnalytic.lean#L123-L229

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
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
open Metric Filter Topology Set Complex MeasureTheory
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_local_extension_09ab203d386c {k : ℕ} {U : Set (Fin k → ℂ)} {g f : (Fin k → ℂ) → ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hf : DifferentiableOn ℂ f (U ∩ {t | g t ≠ 0}))
    (hb : ∀ τ ∈ U, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f '' (N ∩ U ∩ {t | g t ≠ 0})))
    {τ₀ : Fin k → ℂ} (hτ₀ : τ₀ ∈ U) :
    ∃ W ∈ 𝓝 τ₀, ∃ F : (Fin k → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      ∀ τ ∈ W, τ ∈ U → g τ ≠ 0 → F τ = f τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«RiemannExtensionAnalytic».«local_extension» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_local_extension_09ab203d386c
