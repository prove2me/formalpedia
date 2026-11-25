-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_apply_1aabed1ce02b
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_apply_1aabed1ce02b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:56.963797+00:00
-- url     : https://prove2.me/theorems/c523e62e-2b4c-4ea0-8abf-ebff358a5f8a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff apply 1aabed1ce02b: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff apply 1aab
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff apply 1aabed1ce02b construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff apply 1aabed1ce02b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L57-L58

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_apply_1aabed1ce02b (k : ℕ) (y : Fin D → ℂ) :
    chartCutoff k y = Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«chartCutoff_apply» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_apply_1aabed1ce02b
