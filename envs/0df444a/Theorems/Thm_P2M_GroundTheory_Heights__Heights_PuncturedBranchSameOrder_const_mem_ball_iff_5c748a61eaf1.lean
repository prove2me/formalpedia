-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_const_mem_ball_iff_5c748a61eaf1
-- name    : P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_const_mem_ball_iff_5c748a61eaf1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:48.418712+00:00
-- url     : https://prove2.me/theorems/6be96974-6c4b-4061-ba1d-8e9aab4c00d4
-- title:
--   P2 M Ground Theory Heights  Heights Punctured Branch Same Order const mem ball iff 5c748a61eaf1: P2 M Ground Theory Heights  Heights Punctured Branch Same Order const mem ball iff 5c748a61eaf1
-- statement:
--   The P2 M Ground Theory Heights  Heights Punctured Branch Same Order const mem ball iff 5c748a61eaf1 construction uses the P2 M Ground Theory Heights  Heights Punctured Branch Same Order const mem ball iff 5c748a61eaf1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPuncturedBranchSameOrder.lean#L14-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCurveDiscInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchSameOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder

theorem P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_const_mem_ball_iff_5c748a61eaf1 (τ : ℂ) (r : ℝ) :
    (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r ↔ τ ∈ Metric.ball (0 : ℂ) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PuncturedBranchSameOrder».«const_mem_ball_iff» := P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_const_mem_ball_iff_5c748a61eaf1
