-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_unitBall_pos_0862738ceb6b
-- name    : P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_unitBall_pos_0862738ceb6b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:32.417794+00:00
-- url     : https://prove2.me/theorems/663e1652-5c63-4734-aefe-82ca0b905e95
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Graph Lower Density unit Ball pos 0862738ceb6b: P2 M Ground Theory Heights  Heights Tangent Graph Lower Density unit Ball pos 0862738ceb6b
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Graph Lower Density unit Ball pos 0862738ceb6b construction uses the P2 M Ground Theory Heights  Heights Tangent Graph Lower Density unit Ball pos 0862738ceb6b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTangentGraphLowerDensity.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StTangentGraphLowerDensity.lean#L30-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
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
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_unitBall_pos_0862738ceb6b (d : ℕ) :
    0 < μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentGraphLowerDensity».«unitBall_pos» := P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_unitBall_pos_0862738ceb6b
