-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5
-- name    : P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:12.141184+00:00
-- url     : https://prove2.me/theorems/fe4f22ad-872f-4993-af74-014b80b98ba6
-- title:
--   P2 M Ground Theory Heights  Heights Chart Density Integrable Alt exists conj Transpose mul self 3bc270d4f9d5: P2 M Ground Theory Heights  Heights Chart Density Integrable Alt exists conj Transpose mul
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Density Integrable Alt exists conj Transpose mul self 3bc270d4f9d5 construction uses the P2 M Ground Theory Heights  Heights Chart Density Integrable Alt exists conj Transpose mul self 3bc270d4f9d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L16-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L16-L37

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

theorem P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5 {e : ℕ} {N : Matrix (Fin e) (Fin e) ℂ} (hN : N.PosDef) :
    ∃ C : Matrix (Fin e) (Fin e) ℂ, N = Cᴴ * C ∧ C.det ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartDensityIntegrableAlt».«exists_conjTranspose_mul_self» := P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_exists_conjTranspose_mul_self_3bc270d4f9d5
