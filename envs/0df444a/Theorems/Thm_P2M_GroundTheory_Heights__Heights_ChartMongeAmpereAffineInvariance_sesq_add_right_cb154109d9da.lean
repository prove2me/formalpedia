-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_add_right_cb154109d9da
-- name    : P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_add_right_cb154109d9da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:29.146604+00:00
-- url     : https://prove2.me/theorems/87521859-2b52-44b1-8ba2-c1675cd9a205
-- title:
--   P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq add right cb154109d9da: P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq add right cb154109d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq add right cb154109d9da construction uses the P2 M Ground Theory Heights  Heights Chart Monge Ampere Affine Invariance sesq add right cb154109d9da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartMassAffine.lean#L31-L34

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

theorem P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_add_right_cb154109d9da (u v v' : Fin D → ℂ) : sesq H u (v + v') = sesq H u v + sesq H u v' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMongeAmpereAffineInvariance».«sesq_add_right» := P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_sesq_add_right_cb154109d9da
