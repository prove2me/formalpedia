-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_comp_affine_04c215816f18
-- name    : P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_comp_affine_04c215816f18
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:34.305177+00:00
-- url     : https://prove2.me/theorems/b1f9ef74-3542-465c-b5f1-c348029c788e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable comp affine 04c215816f18: P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable comp affine 04c215816f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable comp affine 04c215816f18 construction uses the P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable comp affine 04c215816f18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L118-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L118-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt

theorem P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_comp_affine_04c215816f18 {D : ℕ} {f : (Fin D → ℂ) → ℝ} (hf : Integrable f) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : Integrable (fun y => f (c + P *ᵥ y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartDensityIntegrableAlt».«integrable_comp_affine» := P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_comp_affine_04c215816f18
