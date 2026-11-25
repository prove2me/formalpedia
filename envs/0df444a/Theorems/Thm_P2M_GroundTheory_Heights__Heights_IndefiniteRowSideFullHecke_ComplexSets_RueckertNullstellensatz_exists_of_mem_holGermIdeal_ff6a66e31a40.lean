-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_exists_of_mem_holGermIdeal_ff6a66e31a40
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_exists_of_mem_holGermIdeal_ff6a66e31a40
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:31.431177+00:00
-- url     : https://prove2.me/theorems/ae57cf03-66be-4011-8f56-45e682aa29d7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Rueckert Nullstellensatz exists of mem hol Germ Ideal ff6a66e31a40: P2 M Ground Theory Heights  Heights Indefinite Row S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Rueckert Nullstellensatz exists of mem hol Germ Ideal ff6a66e31a40 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Rueckert Nullstellensatz exists of mem hol Germ Ideal ff6a66e31a40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRueckertNullstellensatz.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRueckertNullstellensatz.lean#L15-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRueckertNullstellensatz
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RueckertNullstellensatz
variable {σ : Type} [Fintype σ] {w : σ → ℂ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_exists_of_mem_holGermIdeal_ff6a66e31a40 {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {φ : holGerms w}
    (hφ : φ ∈ holGermIdeal w p) :
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧
      (φ : Germ (𝓝 w) ℂ) = ((fun z => ∑ i, h i z * p i z : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«RueckertNullstellensatz».«exists_of_mem_holGermIdeal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RueckertNullstellensatz_exists_of_mem_holGermIdeal_ff6a66e31a40
