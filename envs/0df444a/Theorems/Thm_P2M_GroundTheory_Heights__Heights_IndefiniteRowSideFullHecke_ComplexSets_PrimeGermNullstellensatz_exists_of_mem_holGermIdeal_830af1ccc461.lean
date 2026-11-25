-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_exists_of_mem_holGermIdeal_830af1ccc461
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_exists_of_mem_holGermIdeal_830af1ccc461
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:49.219453+00:00
-- url     : https://prove2.me/theorems/90586abd-2fb4-4d98-a7e9-a856b7231aa5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Prime Germ Nullstellensatz exists of mem hol Germ Ideal 830af1ccc461: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Prime Germ Nullstellensatz exists of mem hol Germ Ideal 830af1ccc461 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Prime Germ Nullstellensatz exists of mem hol Germ Ideal 830af1ccc461 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermNullstellensatz.lean#L14-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeGermNullstellensatz.lean#L14-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermCanonicalCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeGermNullstellensatz
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PrimeGermNullstellensatz
variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_exists_of_mem_holGermIdeal_830af1ccc461 {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PrimeGermNullstellensatz».«exists_of_mem_holGermIdeal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimeGermNullstellensatz_exists_of_mem_holGermIdeal_830af1ccc461
