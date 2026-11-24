-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_le_one_40af82f0b80c
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_le_one_40af82f0b80c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:49.724506+00:00
-- url     : https://prove2.me/theorems/6798ca29-16fe-4ea4-8ce5-7cfbc4345ce3
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff le one 40af82f0b80c: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff le one 40
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff le one 40af82f0b80c construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff le one 40af82f0b80c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L67-L67

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_le_one_40af82f0b80c (k : ℕ) (y : Fin D → ℂ) : chartCutoff k y ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«chartCutoff_le_one» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_le_one_40af82f0b80c
