-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_eq_one_644a4a0f61f2
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_eq_one_644a4a0f61f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:50.067191+00:00
-- url     : https://prove2.me/theorems/317ce087-7d3a-4e0f-8918-e657ee1466f4
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff eq one 644a4a0f61f2: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff eq one 64
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff eq one 644a4a0f61f2 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff eq one 644a4a0f61f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L69-L74

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_eq_one_644a4a0f61f2 {k : ℕ} {y : Fin D → ℂ} (h : ∑ i, ‖y i‖ ^ 2 ≤ ((k : ℝ) + 1) ^ 2) :
    chartCutoff k y = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«chartCutoff_eq_one» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_eq_one_644a4a0f61f2
