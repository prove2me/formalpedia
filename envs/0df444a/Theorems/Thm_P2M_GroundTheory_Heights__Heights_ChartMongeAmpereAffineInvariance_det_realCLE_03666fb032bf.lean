-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_realCLE_03666fb032bf
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_realCLE_03666fb032bf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:13.512037+00:00
-- url     : https://prove2.me/theorems/1da1c869-cce7-477c-8eba-06fda10e498a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det real CLE 03666fb032bf: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det real CLE 03666fb032bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det real CLE 03666fb032bf construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance det real CLE 03666fb032bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L165-L172

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_realCLE_03666fb032bf (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) :
    LinearMap.det ((realCLE P hP : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      Complex.normSq P.det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«det_realCLE» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_det_realCLE_03666fb032bf
