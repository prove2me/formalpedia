-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_punctured_branch_7f894f3acf71
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_punctured_branch_7f894f3acf71
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:20.506104+00:00
-- url     : https://prove2.me/theorems/950a765f-6ac3-416e-a477-8c953803aa26
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred Disc Cover punctured branch 7f894f3acf71: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Com
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred Disc Cover punctured branch 7f894f3acf71 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets centred Disc Cover punctured branch 7f894f3acf71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCentredDiscCoverCurve.lean#L12-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCentredDiscCoverCurve.lean#L12-L116

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_punctured_branch_7f894f3acf71 (hPCC : PuncturedCoverCycles.Statement)
    {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {p : (σ → ℂ) →L[ℂ] ℂ} {ρ : ℝ} {N : ℕ}
    (hY : IsCentredDiscCover Y w p ρ N) :
    ∃ (δ : ℝ) (k : ℕ) (φ : ℂ → σ → ℂ), 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ k ∧
      DifferentiableOn ℂ φ (ball 0 δ \ {0}) ∧ Set.InjOn φ (ball 0 δ \ {0}) ∧
      ∀ s ∈ ball (0 : ℂ) δ \ {0}, φ s ∈ Y ∧ p (φ s) = p w + s ^ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«centredDiscCover_punctured_branch» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_centredDiscCover_punctured_branch_7f894f3acf71
