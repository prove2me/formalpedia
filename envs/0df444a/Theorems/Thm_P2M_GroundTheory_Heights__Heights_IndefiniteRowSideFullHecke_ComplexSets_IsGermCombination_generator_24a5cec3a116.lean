-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_generator_24a5cec3a116
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_generator_24a5cec3a116
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:52.329146+00:00
-- url     : https://prove2.me/theorems/4069cae5-3635-422c-825d-36a43b9323e4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Germ Combination generator 24a5cec3a116: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Germ Combination generator 24a5cec3a116 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Is Germ Combination generator 24a5cec3a116 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
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
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsGermCombination
variable {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_generator_24a5cec3a116 (i : Fin k) : IsGermCombination w p (p i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«IsGermCombination».«generator» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsGermCombination_generator_24a5cec3a116
