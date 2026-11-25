-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_re_star_dotProduct_self_cd96284eeba4
-- name    : P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_re_star_dotProduct_self_cd96284eeba4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:40.524497+00:00
-- url     : https://prove2.me/theorems/98e6fc88-2fa2-4ebf-9f02-58ed5c6d3c00
-- title:
--   P2 M Ground Theory Heights  Heights Chart Density Integrable Alt re star dot Product self cd96284eeba4: P2 M Ground Theory Heights  Heights Chart Density Integrable Alt re star dot Product self cd9628
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Density Integrable Alt re star dot Product self cd96284eeba4 construction uses the P2 M Ground Theory Heights  Heights Chart Density Integrable Alt re star dot Product self cd96284eeba4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L55-L58

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

theorem P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_re_star_dotProduct_self_cd96284eeba4 {e : ℕ} (z : Fin e → ℂ) : (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartDensityIntegrableAlt».«re_star_dotProduct_self» := P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_re_star_dotProduct_self_cd96284eeba4
