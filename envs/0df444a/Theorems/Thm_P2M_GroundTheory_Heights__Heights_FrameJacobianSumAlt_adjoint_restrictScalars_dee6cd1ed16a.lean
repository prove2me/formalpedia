-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_adjoint_restrictScalars_dee6cd1ed16a
-- name    : P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_adjoint_restrictScalars_dee6cd1ed16a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:21.528198+00:00
-- url     : https://prove2.me/theorems/38c8db84-3529-4c59-aee4-1bd5c50e8d23
-- title:
--   P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt adjoint restrict Scalars dee6cd1ed16a: P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt adjoint restrict Scalars dee6cd1ed16a
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt adjoint restrict Scalars dee6cd1ed16a construction uses the P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt adjoint restrict Scalars dee6cd1ed16a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L19-L25

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

theorem P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_adjoint_restrictScalars_dee6cd1ed16a (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.adjoint (S.restrictScalars ℝ) = (LinearMap.adjoint S).restrictScalars ℝ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameJacobianSumAlt».«adjoint_restrictScalars» := P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_adjoint_restrictScalars_dee6cd1ed16a
