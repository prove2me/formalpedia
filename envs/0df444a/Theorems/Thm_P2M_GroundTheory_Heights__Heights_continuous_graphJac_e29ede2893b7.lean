-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_graphJac_e29ede2893b7
-- name    : P2M_GroundTheory_Heights__Heights_continuous_graphJac_e29ede2893b7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:17.074822+00:00
-- url     : https://prove2.me/theorems/7b4eb48a-83df-5302-bc08-c0c5cecc6927
-- title:
--   P2 M Ground Theory Heights  Heights continuous graph Jac e29ede2893b7: P2 M Ground Theory Heights  Heights continuous graph Jac e29ede2893b7
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous graph Jac e29ede2893b7 construction uses the P2 M Ground Theory Heights  Heights continuous graph Jac e29ede2893b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphJacContinuous.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphJacContinuous.lean#L39-L53

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

theorem P2M_GroundTheory_Heights__Heights_continuous_graphJac_e29ede2893b7 (k m : ℕ) :
    Continuous fun B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) =>
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_graphJac» := P2M_GroundTheory_Heights__Heights_continuous_graphJac_e29ede2893b7
