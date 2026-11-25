-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphJac_pos_8f8be9a41ec1
-- name    : P2M_GroundTheory_Heights__Heights_graphJac_pos_8f8be9a41ec1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:26.972341+00:00
-- url     : https://prove2.me/theorems/227ee59d-bd64-5b8a-8020-aba7ce8060ab
-- title:
--   P2 M Ground Theory Heights  Heights graph Jac pos 8f8be9a41ec1: P2 M Ground Theory Heights  Heights graph Jac pos 8f8be9a41ec1
-- statement:
--   The P2 M Ground Theory Heights  Heights graph Jac pos 8f8be9a41ec1 construction uses the P2 M Ground Theory Heights  Heights graph Jac pos 8f8be9a41ec1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphJacContinuous.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphJacContinuous.lean#L35-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
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
noncomputable section
open scoped InnerProductSpace

theorem P2M_GroundTheory_Heights__Heights_graphJac_pos_8f8be9a41ec1 {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < graphJac B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«graphJac_pos» := P2M_GroundTheory_Heights__Heights_graphJac_pos_8f8be9a41ec1
