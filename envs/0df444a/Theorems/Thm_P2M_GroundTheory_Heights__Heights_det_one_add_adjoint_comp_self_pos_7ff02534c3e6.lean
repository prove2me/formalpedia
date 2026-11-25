-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_one_add_adjoint_comp_self_pos_7ff02534c3e6
-- name    : P2M_GroundTheory_Heights__Heights_det_one_add_adjoint_comp_self_pos_7ff02534c3e6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:36.3598+00:00
-- url     : https://prove2.me/theorems/425c608c-8b43-439a-a2fe-3d36dd0d80b6
-- title:
--   P2 M Ground Theory Heights  Heights det one add adjoint comp self pos 7ff02534c3e6: P2 M Ground Theory Heights  Heights det one add adjoint comp self pos 7ff02534c3e6
-- statement:
--   The P2 M Ground Theory Heights  Heights det one add adjoint comp self pos 7ff02534c3e6 construction uses the P2 M Ground Theory Heights  Heights det one add adjoint comp self pos 7ff02534c3e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphJacContinuous.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphJacContinuous.lean#L11-L33

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

theorem P2M_GroundTheory_Heights__Heights_det_one_add_adjoint_comp_self_pos_7ff02534c3e6 {k m : ℕ}
    (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    0 < LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
      LinearMap.adjoint B ∘ₗ B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_one_add_adjoint_comp_self_pos» := P2M_GroundTheory_Heights__Heights_det_one_add_adjoint_comp_self_pos_7ff02534c3e6
