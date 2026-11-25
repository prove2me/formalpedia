-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_right_7969de32b78f
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_right_7969de32b78f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:27.576475+00:00
-- url     : https://prove2.me/theorems/b96d684a-a2ea-4211-bf14-06c2c49c9041
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I right 7969de32b78f: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I right 7969de32b78f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I right 7969de32b78f construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I right 7969de32b78f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L52-L56

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
variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_right_7969de32b78f (u v : Fin D → ℂ) : sesq H u (Complex.I • v) = -Complex.I * sesq H u v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«sesq_I_right» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_right_7969de32b78f
