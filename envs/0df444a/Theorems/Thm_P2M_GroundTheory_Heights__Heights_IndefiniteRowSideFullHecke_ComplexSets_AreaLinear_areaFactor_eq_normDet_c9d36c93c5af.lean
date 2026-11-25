-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AreaLinear_areaFactor_eq_normDet_c9d36c93c5af
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AreaLinear_areaFactor_eq_normDet_c9d36c93c5af
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:04.809222+00:00
-- url     : https://prove2.me/theorems/9a179d2f-b00f-4246-85e1-294314a444d1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Area Linear area Factor eq norm Det c9d36c93c5af: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Com
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Area Linear area Factor eq norm Det c9d36c93c5af construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Area Linear area Factor eq norm Det c9d36c93c5af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/VolumeLtHausdorffUnitBallTwenty.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/VolumeLtHausdorffUnitBallTwenty.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FrameProjEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
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
open MeasureTheory Measure Metric Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AreaLinear_areaFactor_eq_normDet_c9d36c93c5af {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    areaFactor L = L.normDet := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«AreaLinear».«areaFactor_eq_normDet» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AreaLinear_areaFactor_eq_normDet_c9d36c93c5af
