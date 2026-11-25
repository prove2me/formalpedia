-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_fibre_unique_near_7ec4b92fbfb3
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_fibre_unique_near_7ec4b92fbfb3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:52.196258+00:00
-- url     : https://prove2.me/theorems/52742fa4-1fb5-4959-a6f6-abe94b654fc0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Maximal Count Unbranched fibre unique near 7ec4b92fbfb3: P2 M Ground Theory Heights  Heights Indefinite Row Side Full He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Maximal Count Unbranched fibre unique near 7ec4b92fbfb3 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Maximal Count Unbranched fibre unique near 7ec4b92fbfb3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaximalCountUnbranched.lean#L24-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaximalCountUnbranched.lean#L24-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaximalCountUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaximalCountUnbranched
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
open Topology Filter Metric
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_fibre_unique_near_7ec4b92fbfb3 {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {N : ℕ} (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {z : σ → ℂ} (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ W ∈ 𝓝 (A z), ∀ y ∈ W,
      {x' | x' ∈ Y ∧ A x' = y}.encard = N ∧ (∃ x' ∈ Y, A x' = y ∧ dist x' z < ε) ∧
      ∀ x₁ ∈ Y, ∀ x₂ ∈ Y, A x₁ = y → A x₂ = y → dist x₁ z < ε → dist x₂ z < ε → x₁ = x₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«MaximalCountUnbranched».«fibre_unique_near» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_fibre_unique_near_7ec4b92fbfb3
