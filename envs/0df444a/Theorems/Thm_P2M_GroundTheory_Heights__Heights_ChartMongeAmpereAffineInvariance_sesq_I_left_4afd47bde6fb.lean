-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_left_4afd47bde6fb
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_left_4afd47bde6fb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:29.24458+00:00
-- url     : https://prove2.me/theorems/b5054e7f-4f87-551f-b735-aecfb91c1851
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I left 4afd47bde6fb: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I left 4afd47bde6fb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I left 4afd47bde6fb construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq I left 4afd47bde6fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L46-L50

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_left_4afd47bde6fb (u v : Fin D → ℂ) : sesq H (Complex.I • u) v = Complex.I * sesq H u v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«sesq_I_left» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_I_left_4afd47bde6fb
