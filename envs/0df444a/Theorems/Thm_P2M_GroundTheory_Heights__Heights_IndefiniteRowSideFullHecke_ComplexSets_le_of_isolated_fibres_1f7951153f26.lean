-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_le_of_isolated_fibres_1f7951153f26
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_le_of_isolated_fibres_1f7951153f26
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:53.205855+00:00
-- url     : https://prove2.me/theorems/31e5a899-c3a5-48d7-9f1f-32f585810439
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets le of isolated fibres 1f7951153f26: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets le o
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets le of isolated fibres 1f7951153f26 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets le of isolated fibres 1f7951153f26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermProjectionImageNear.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermProjectionImageNear.lean#L14-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermProjectionImageNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermProjectionImageNear
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
open Topology Filter Metric Set

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_le_of_isolated_fibres_1f7951153f26 (hfi : HolomorphicFibreInfinite.Statement) {e d : ℕ} {O : Set (Fin e → ℂ)}
    {φ : (Fin e → ℂ) → Fin d → ℂ} (hO : IsOpen O) (hne : O.Nonempty) (hφ : DifferentiableOn ℂ φ O)
    (hiso : ∀ t ∈ O, ∃ W ∈ 𝓝 t, ∀ v ∈ W, v ∈ O → φ v = φ t → v = t) : e ≤ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«le_of_isolated_fibres» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_le_of_isolated_fibres_1f7951153f26
