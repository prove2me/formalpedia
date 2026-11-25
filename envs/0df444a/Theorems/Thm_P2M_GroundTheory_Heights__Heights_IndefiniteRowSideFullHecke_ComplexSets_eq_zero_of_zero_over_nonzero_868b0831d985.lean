-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_zero_over_nonzero_868b0831d985
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_zero_over_nonzero_868b0831d985
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:23.027957+00:00
-- url     : https://prove2.me/theorems/d188188a-51be-50a7-8c8f-901e9b75a8e8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero of zero over nonzero 868b0831d985: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero of zero over nonzero 868b0831d985 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq zero of zero over nonzero 868b0831d985 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L156-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L156-L175

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_zero_over_nonzero_868b0831d985 {σ : Type} [Fintype σ] {k : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (D : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → ℂ) (hWo : IsOpen W)
    (hDo : IsOpen D) (hgne : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, g t ≠ 0)
    (hopen : ∀ z ∈ Z ∩ W, ∀ ε > 0, A '' (Z ∩ Metric.ball z ε) ∈ 𝓝 (A z)) {x : σ → ℂ} (hx : x ∈ Z ∩ W)
    (hAx : A x ∈ D) (Ψ : (σ → ℂ) → ℂ) (hΨ : ContinuousAt Ψ x) (V₀ : Set (σ → ℂ)) (hV₀ : V₀ ∈ 𝓝 x)
    (h0 : ∀ z ∈ Z ∩ W ∩ V₀, A z ∈ D → g (A z) ≠ 0 → Ψ z = 0) : Ψ x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eq_zero_of_zero_over_nonzero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_zero_of_zero_over_nonzero_868b0831d985
