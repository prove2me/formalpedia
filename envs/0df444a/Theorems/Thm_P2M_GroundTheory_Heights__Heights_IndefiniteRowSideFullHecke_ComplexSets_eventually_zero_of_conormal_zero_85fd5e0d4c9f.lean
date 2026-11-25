-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_conormal_zero_85fd5e0d4c9f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_conormal_zero_85fd5e0d4c9f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:54.160221+00:00
-- url     : https://prove2.me/theorems/13d72172-ccb8-47e9-a784-e90ead6e69c5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually zero of conormal zero 85fd5e0d4c9f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comple
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually zero of conormal zero 85fd5e0d4c9f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually zero of conormal zero 85fd5e0d4c9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L36-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L36-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense
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
open Topology Filter Module
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_conormal_zero_85fd5e0d4c9f {C : Set E} {y₀ : E} (hy₀ : y₀ ∈ C) {U : Set E} (hU : U ∈ 𝓝 y₀)
    (hC : ∀ c ∈ C ∩ U, ∀ ψ : E → ℂ, AnalyticAt ℂ ψ c → (∀ᶠ u in 𝓝 c, u ∈ C → ψ u = 0) →
      fderiv ℂ ψ c = 0)
    {ψ : E → ℂ} (hψ : AnalyticAt ℂ ψ y₀) (hψC : ∀ᶠ u in 𝓝 y₀, u ∈ C → ψ u = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eventually_zero_of_conormal_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_conormal_zero_85fd5e0d4c9f
