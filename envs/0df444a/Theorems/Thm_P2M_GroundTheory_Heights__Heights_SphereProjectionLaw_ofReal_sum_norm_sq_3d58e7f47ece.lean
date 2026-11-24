-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_sum_norm_sq_3d58e7f47ece
-- name    : P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_sum_norm_sq_3d58e7f47ece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:09.30109+00:00
-- url     : https://prove2.me/theorems/079e6d35-4c0d-4522-a338-f8dcd3d09022
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Projection Law of Real sum norm sq 3d58e7f47ece: P2 M Ground Theory Heights  Heights Sphere Projection Law of Real sum norm sq 3d58e7f47ece
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Projection Law of Real sum norm sq 3d58e7f47ece construction uses the P2 M Ground Theory Heights  Heights Sphere Projection Law of Real sum norm sq 3d58e7f47ece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereProjectionLaw.lean#L18-L21

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

theorem P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_sum_norm_sq_3d58e7f47ece (v : Fin n → ℂ) :
    ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) = ∑ j, v j * star (v j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereProjectionLaw».«ofReal_sum_norm_sq» := P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_ofReal_sum_norm_sq_3d58e7f47ece
