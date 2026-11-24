-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559
-- name    : P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:53.583399+00:00
-- url     : https://prove2.me/theorems/ca4fbd2c-150c-44ca-9404-ce3a45eb7520
-- title:
--   P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt det adjoint comp cac87e9cc559: P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt det adjoint comp cac87e9cc559
-- statement:
--   The P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt det adjoint comp cac87e9cc559 construction uses the P2 M Ground Theory Heights  Heights Frame Jacobian Sum Alt det adjoint comp cac87e9cc559 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFrameJacobianSum.lean#L32-L41

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

theorem P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559 (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.det (LinearMap.adjoint S ∘ₗ S) =
      (Matrix.of fun i j : Fin d => inner ℂ (S (EuclideanSpace.basisFun (Fin d) ℂ i))
        (S (EuclideanSpace.basisFun (Fin d) ℂ j))).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FrameJacobianSumAlt».«det_adjoint_comp» := P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559
