-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_sum_right_5baa8579accc
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_sum_right_5baa8579accc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:42.558621+00:00
-- url     : https://prove2.me/theorems/6a754eb3-5bc2-46c9-9376-9b805d4ea0a4
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq sum right 5baa8579accc: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq sum right 5baa8579ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq sum right 5baa8579accc construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq sum right 5baa8579accc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L79-L81

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_sum_right_5baa8579accc (u : Fin D → ℂ) (v : Fin D → Fin D → ℂ) :
    sesq H u (∑ l, v l) = ∑ l, sesq H u (v l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«sesq_sum_right» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_sum_right_5baa8579accc
