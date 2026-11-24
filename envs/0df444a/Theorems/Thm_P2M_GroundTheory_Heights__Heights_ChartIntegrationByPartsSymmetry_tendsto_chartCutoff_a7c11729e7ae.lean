-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_tendsto_chartCutoff_a7c11729e7ae
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_tendsto_chartCutoff_a7c11729e7ae
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:40.60935+00:00
-- url     : https://prove2.me/theorems/3e5f200e-4785-4b1c-ab19-29b54ad7cb49
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry tendsto chart Cutoff a7c11729e7ae: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry tendsto chart Cutoff
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry tendsto chart Cutoff a7c11729e7ae construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry tendsto chart Cutoff a7c11729e7ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L94-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartCutoffParts
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntegrationByPartsSymmetry
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_tendsto_chartCutoff_a7c11729e7ae (y : Fin D → ℂ) : Tendsto (fun k : ℕ => chartCutoff k y) atTop (𝓝 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«tendsto_chartCutoff» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_tendsto_chartCutoff_a7c11729e7ae
