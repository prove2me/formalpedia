-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ball_indicator_le_6727de79cc83
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ball_indicator_le_6727de79cc83
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:31.893827+00:00
-- url     : https://prove2.me/theorems/1d4234f5-fe4f-44eb-8f86-01114038d056
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail ball indicator le 6727de79cc83: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail ball indicator le 6727de79cc83
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail ball indicator le 6727de79cc83 construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail ball indicator le 6727de79cc83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L186-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L186-L200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ball_indicator_le_6727de79cc83 {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) ≤
      ∏ i, ballInd r (π i c0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«ball_indicator_le» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_ball_indicator_le_6727de79cc83
