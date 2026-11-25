-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularPointOf_ball_b673d809f104
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularPointOf_ball_b673d809f104
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:19.151003+00:00
-- url     : https://prove2.me/theorems/2e115a90-7f86-4202-b60d-067b599bf7a7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Regular Point Of ball b673d809f104: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets i
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Regular Point Of ball b673d809f104 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Regular Point Of ball b673d809f104 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPointsOffDiscriminant.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PIrreducibleGermPointsOffDiscriminant.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPointsOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedPointsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPointsOffDiscriminant
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
open Topology Metric Filter Set

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularPointOf_ball_b673d809f104 {d : ℕ} (c : Fin d → ℂ) (ε : ℝ) :
    ∀ y ∈ ball c ε, IsRegularPointOf (ball c ε) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«isRegularPointOf_ball» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularPointOf_ball_b673d809f104
