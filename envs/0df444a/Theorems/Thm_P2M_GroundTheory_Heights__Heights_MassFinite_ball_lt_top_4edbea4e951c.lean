-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MassFinite_ball_lt_top_4edbea4e951c
-- name    : P2M_GroundTheory_Heights__Heights_MassFinite_ball_lt_top_4edbea4e951c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:48:19.656233+00:00
-- url     : https://prove2.me/theorems/93b3465f-094f-4375-bbed-2d4ced9b7f3d
-- title:
--   P2 M Ground Theory Heights  Heights Mass Finite ball lt top 4edbea4e951c: P2 M Ground Theory Heights  Heights Mass Finite ball lt top 4edbea4e951c
-- statement:
--   The P2 M Ground Theory Heights  Heights Mass Finite ball lt top 4edbea4e951c construction uses the P2 M Ground Theory Heights  Heights Mass Finite ball lt top 4edbea4e951c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L65-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L65-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite

theorem P2M_GroundTheory_Heights__Heights_MassFinite_ball_lt_top_4edbea4e951c {ι : Type*} [Fintype ι] (R : ℝ) :
    μH[((2 * Fintype.card ι : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R) < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MassFinite».«ball_lt_top» := P2M_GroundTheory_Heights__Heights_MassFinite_ball_lt_top_4edbea4e951c
