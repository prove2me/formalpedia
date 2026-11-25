-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_extend_across_centre_fff121512849
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_extend_across_centre_fff121512849
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:52.331807+00:00
-- url     : https://prove2.me/theorems/418a1987-c2cf-43d3-b8af-c8ae3410ee91
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred Disc Cover extend across centre fff121512849: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred Disc Cover extend across centre fff121512849 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred Disc Cover extend across centre fff121512849 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCentredDiscCoverCurve.lean#L118-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCentredDiscCoverCurve.lean#L118-L197

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCentredDiscCoverCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCoverCycles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCentredDiscCoverCurve
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
open Topology Filter Metric Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_extend_across_centre_fff121512849
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) {δ : ℝ} {k : ℕ} {φ : ℂ → σ → ℂ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 1 ≤ k) (hφd : DifferentiableOn ℂ φ (ball 0 δ \ {0})) (hφi : Set.InjOn φ (ball 0 δ \ {0}))
    (hφY : ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k) :
    ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
      DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«centredDiscCover_extend_across_centre» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_extend_across_centre_fff121512849
