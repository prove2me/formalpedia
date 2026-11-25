-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_real_smul_right_0c1e1a8c5690
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_real_smul_right_0c1e1a8c5690
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:42.348798+00:00
-- url     : https://prove2.me/theorems/01997838-7b4c-4ff6-9e2f-97cff1708dcc
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq real smul right 0c1e1a8c5690: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq real smul righ
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq real smul right 0c1e1a8c5690 construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq real smul right 0c1e1a8c5690 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L41-L44

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_real_smul_right_0c1e1a8c5690 (r : ℝ) (u v : Fin D → ℂ) : sesq H u (r • v) = r * sesq H u v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«sesq_real_smul_right» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_real_smul_right_0c1e1a8c5690
