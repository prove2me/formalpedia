-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_slice_cauchy_2d945a37a135
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_slice_cauchy_2d945a37a135
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:08.48245+00:00
-- url     : https://prove2.me/theorems/937e3db5-c1da-4671-a4ac-d66feb1eaab0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic slice cauchy 2d945a37a135: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic slice cauchy 2d945a37a135 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Riemann Extension Analytic slice cauchy 2d945a37a135 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRiemannExtensionAnalytic.lean#L70-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRiemannExtensionAnalytic.lean#L70-L121

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_slice_cauchy_2d945a37a135 {R ρ : ℝ} {ψ h : ℂ → ℂ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hψ : DifferentiableOn ℂ ψ (ball 0 R)) (hsph : ∀ z ∈ sphere (0 : ℂ) ρ, ψ z ≠ 0) (hψ0 : ψ 0 ≠ 0)
    (hh : ∀ z ∈ ball (0 : ℂ) R, ψ z ≠ 0 → DifferentiableAt ℂ h z)
    (hb : ∀ z ∈ ball (0 : ℂ) R, ∃ N ∈ 𝓝 z, ∃ C, ∀ w ∈ N, w ∈ ball (0 : ℂ) R → ψ w ≠ 0 → ‖h w‖ ≤ C) :
    (2 * π * I : ℂ)⁻¹ • (∮ z in C(0, ρ), z⁻¹ • h z) = h 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«RiemannExtensionAnalytic».«slice_cauchy» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_slice_cauchy_2d945a37a135
