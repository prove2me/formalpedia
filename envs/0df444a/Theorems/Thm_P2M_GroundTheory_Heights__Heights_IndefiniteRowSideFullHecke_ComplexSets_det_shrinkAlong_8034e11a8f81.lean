-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_shrinkAlong_8034e11a8f81
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_shrinkAlong_8034e11a8f81
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:37.788433+00:00
-- url     : https://prove2.me/theorems/94d9f9ef-a3f3-4aff-bed1-7d86eaf8906c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets det shrink Along 8034e11a8f81: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets det shrin
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets det shrink Along 8034e11a8f81 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets det shrink Along 8034e11a8f81 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L24-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L24-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
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
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_shrinkAlong_8034e11a8f81 (i0 : ι) (k : ι → ℝ) (δ : ℝ) :
    LinearMap.det (shrinkAlong i0 k δ) = 1 - (1 - δ) * k i0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«det_shrinkAlong» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_shrinkAlong_8034e11a8f81
