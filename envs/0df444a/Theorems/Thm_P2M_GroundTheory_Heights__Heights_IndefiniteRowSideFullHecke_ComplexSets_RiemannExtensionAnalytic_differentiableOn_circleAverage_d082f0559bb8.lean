-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_differentiableOn_circleAverage_d082f0559bb8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_differentiableOn_circleAverage_d082f0559bb8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:37.59085+00:00
-- url     : https://prove2.me/theorems/87953a81-44d3-55ad-990d-7654ec9943cf
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic differentiable On circle Average d082f0559bb8: P2 M Ground Theory Heights  Heights Indefinite
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic differentiable On circle Average d082f0559bb8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic differentiable On circle Average d082f0559bb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRiemannExtensionAnalytic.lean#L32-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRiemannExtensionAnalytic.lean#L32-L68

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_differentiableOn_circleAverage_d082f0559bb8 {k : ℕ} {O : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → ℂ}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) {τ₀ v : Fin k → ℂ} {ρ δ : ℝ} (hρ : 0 ≤ ρ)
    (hK : ∀ τ ∈ closedBall τ₀ δ, ∀ z ∈ sphere (0 : ℂ) ρ, τ + z • v ∈ O) :
    DifferentiableOn ℂ (fun τ => ∫ θ in (0 : ℝ)..2 * π, f (τ + circleMap 0 ρ θ • v)) (ball τ₀ δ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«RiemannExtensionAnalytic».«differentiableOn_circleAverage» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_differentiableOn_circleAverage_d082f0559bb8
