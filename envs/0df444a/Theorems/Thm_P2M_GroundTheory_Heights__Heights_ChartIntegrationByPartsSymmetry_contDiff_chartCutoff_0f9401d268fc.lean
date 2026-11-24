-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_chartCutoff_0f9401d268fc
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_chartCutoff_0f9401d268fc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:54.205867+00:00
-- url     : https://prove2.me/theorems/dc8aa9ac-d0bf-40e0-bda1-d6b26c78aac5
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff chart Cutoff 0f9401d268fc: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff chart Cut
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff chart Cutoff 0f9401d268fc construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff chart Cutoff 0f9401d268fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L60-L63

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_chartCutoff_0f9401d268fc (k : ℕ) (m : ℕ) : ContDiff ℝ m (chartCutoff (D := D) k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«contDiff_chartCutoff» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_chartCutoff_0f9401d268fc
