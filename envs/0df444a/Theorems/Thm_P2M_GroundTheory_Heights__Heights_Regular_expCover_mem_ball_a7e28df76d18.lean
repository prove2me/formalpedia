-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_expCover_mem_ball_a7e28df76d18
-- name    : P2M_GroundTheory_Heights__Heights_Regular_expCover_mem_ball_a7e28df76d18
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:55.520599+00:00
-- url     : https://prove2.me/theorems/8f687edd-ce5b-4aa2-bf94-8cb5996b10a5
-- title:
--   P2 M Ground Theory Heights  Heights Regular exp Cover mem ball a7e28df76d18: P2 M Ground Theory Heights  Heights Regular exp Cover mem ball a7e28df76d18
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular exp Cover mem ball a7e28df76d18 construction uses the P2 M Ground Theory Heights  Heights Regular exp Cover mem ball a7e28df76d18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L123-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L123-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_expCover_mem_ball_a7e28df76d18 {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    expCover a w ∈ ball (0 : Fin n → ℂ) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«expCover_mem_ball» := P2M_GroundTheory_Heights__Heights_Regular_expCover_mem_ball_a7e28df76d18
