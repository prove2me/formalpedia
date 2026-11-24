-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91
-- name    : P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:43.937833+00:00
-- url     : https://prove2.me/theorems/24c93100-1184-489c-9b59-cda87e72879a
-- title:
--   P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt area Jacobian restrict Scalars 31766ed81e91: P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt area Jacobian restrict Scalars 31766e
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt area Jacobian restrict Scalars 31766ed81e91 construction uses the P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt area Jacobian restrict Scalars 31766ed81e91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L27-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
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
open Matrix Finset Module
noncomputable section
open GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91 (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    areaJacobian (S.restrictScalars ℝ) = ‖LinearMap.det (LinearMap.adjoint S ∘ₗ S)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameJacobianSumAlt».«areaJacobian_restrictScalars» := P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91
