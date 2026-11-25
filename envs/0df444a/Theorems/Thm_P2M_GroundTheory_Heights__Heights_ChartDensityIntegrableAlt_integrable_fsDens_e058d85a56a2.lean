-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_fsDens_e058d85a56a2
-- name    : P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_fsDens_e058d85a56a2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:35.206371+00:00
-- url     : https://prove2.me/theorems/3d06bb95-bd9a-4a04-8743-4990b62c0fb6
-- title:
--   P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable fs Dens e058d85a56a2: P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable fs Dens e058d85a56a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable fs Dens e058d85a56a2 construction uses the P2 M Ground Theory Heights  Heights Chart Density Integrable Alt integrable fs Dens e058d85a56a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L104-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L104-L116

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

theorem P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_fsDens_e058d85a56a2 (D : ℕ) :
    Integrable (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartDensityIntegrableAlt».«integrable_fsDens» := P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_integrable_fsDens_e058d85a56a2
