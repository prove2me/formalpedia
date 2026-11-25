-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentJacComp_adjoint_restrictScalars_6c2dd86bcf0a
-- name    : P2M_GroundTheory_Heights__Heights_TangentJacComp_adjoint_restrictScalars_6c2dd86bcf0a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:07.378414+00:00
-- url     : https://prove2.me/theorems/8d2a4d35-681d-4c7c-b2c9-1def4d72562a
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Jac Comp adjoint restrict Scalars 6c2dd86bcf0a: P2 M Ground Theory Heights  Heights Tangent Jac Comp adjoint restrict Scalars 6c2dd86bcf0a
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Jac Comp adjoint restrict Scalars 6c2dd86bcf0a construction uses the P2 M Ground Theory Heights  Heights Tangent Jac Comp adjoint restrict Scalars 6c2dd86bcf0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacComp.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacComp.lean#L13-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacComp
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

theorem P2M_GroundTheory_Heights__Heights_TangentJacComp_adjoint_restrictScalars_6c2dd86bcf0a {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    LinearMap.adjoint (L.restrictScalars ℝ) = (LinearMap.adjoint L).restrictScalars ℝ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentJacComp».«adjoint_restrictScalars» := P2M_GroundTheory_Heights__Heights_TangentJacComp_adjoint_restrictScalars_6c2dd86bcf0a
