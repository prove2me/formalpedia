-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_sub_ddb4e8b7c1b8
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_sub_ddb4e8b7c1b8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:39:47.449608+00:00
-- url     : https://prove2.me/theorems/e17769eb-1cda-4dd3-abf2-827a8532198f
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq sub ddb4e8b7c1b8: P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq sub ddb4e8b7c1b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq sub ddb4e8b7c1b8 construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law sum norm sq sub ddb4e8b7c1b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L41-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L41-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
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
open MeasureTheory ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.SphereProjectionLaw
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_sub_ddb4e8b7c1b8 {p z : Fin n → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hz : ∑ j, ‖z j‖ ^ 2 = 1) :
    ∑ j, ‖(z - coordAlong p z • p) j‖ ^ 2 = 1 - ‖coordAlong p z‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«sum_norm_sq_sub» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_sub_ddb4e8b7c1b8
