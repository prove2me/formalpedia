-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_bot_d24e95e81a5c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_bot_d24e95e81a5c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:18.159602+00:00
-- url     : https://prove2.me/theorems/97becc14-4e00-4fe7-ad83-cf03e859abe5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Finite Germ Projection bot d24e95e81a5c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Finite Germ Projection bot d24e95e81a5c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Finite Germ Projection bot d24e95e81a5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteGermProjectionObjects.lean#L23-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteGermProjectionObjects.lean#L23-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionObjects
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_bot_d24e95e81a5c {σ : Type} [Fintype σ] (w : σ → ℂ) :
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w ⊥ A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«isFiniteGermProjection_bot» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isFiniteGermProjection_bot_d24e95e81a5c
