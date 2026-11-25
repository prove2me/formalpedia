-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_mem_vanishingIdeal_iff_9bd4e1e9bd60
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_mem_vanishingIdeal_iff_9bd4e1e9bd60
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:43.802816+00:00
-- url     : https://prove2.me/theorems/3157ad9a-422b-4780-80ce-668547888de7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components mem vanishing Ideal iff 9bd4e1e9bd60: P2 M Ground Theory Heights  Heights Indefinite Row Side F
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components mem vanishing Ideal iff 9bd4e1e9bd60 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components mem vanishing Ideal iff 9bd4e1e9bd60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L35-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_mem_vanishingIdeal_iff_9bd4e1e9bd60 {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) :
    (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal X w ↔ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«AnalyticGermComponents».«mem_vanishingIdeal_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_mem_vanishingIdeal_iff_9bd4e1e9bd60
