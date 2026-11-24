-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_eq_sesq_4253c4c2c89e
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_eq_sesq_4253c4c2c89e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:16.211061+00:00
-- url     : https://prove2.me/theorems/fe6e45b8-8991-40d9-8957-3b892586c490
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian eq sesq 4253c4c2c89e: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian eq sesq 42
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian eq sesq 4253c4c2c89e construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance cx Hessian eq sesq 4253c4c2c89e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L19-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMongeAmpereAffineInvariance
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_eq_sesq_4253c4c2c89e (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (i j : Fin D) :
    cxHessian f z i j = sesq (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«cxHessian_eq_sesq» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_cxHessian_eq_sesq_4253c4c2c89e
