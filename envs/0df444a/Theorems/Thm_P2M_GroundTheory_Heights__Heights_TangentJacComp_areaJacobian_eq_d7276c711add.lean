-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentJacComp_areaJacobian_eq_d7276c711add
-- name    : P2M_GroundTheory_Heights__Heights_TangentJacComp_areaJacobian_eq_d7276c711add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:54.577291+00:00
-- url     : https://prove2.me/theorems/033da047-8146-4565-9e3a-6257d970ee72
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Jac Comp area Jacobian eq d7276c711add: P2 M Ground Theory Heights  Heights Tangent Jac Comp area Jacobian eq d7276c711add
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Jac Comp area Jacobian eq d7276c711add construction uses the P2 M Ground Theory Heights  Heights Tangent Jac Comp area Jacobian eq d7276c711add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacComp.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacComp.lean#L22-L30

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

theorem P2M_GroundTheory_Heights__Heights_TangentJacComp_areaJacobian_eq_d7276c711add {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    areaJacobian (L.restrictScalars ℝ) = L.normDet ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentJacComp».«areaJacobian_eq» := P2M_GroundTheory_Heights__Heights_TangentJacComp_areaJacobian_eq_d7276c711add
