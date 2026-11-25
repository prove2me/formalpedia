-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_mono_2f4f957da48a
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_mono_2f4f957da48a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:05.773732+00:00
-- url     : https://prove2.me/theorems/a2a61d1e-9f2b-48fc-9100-b99a61d7be69
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff mono 2f4f957da48a: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff mono 2f4f95
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff mono 2f4f957da48a construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry chart Cutoff mono 2f4f957da48a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L83-L92

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_mono_2f4f957da48a (y : Fin D → ℂ) : Monotone fun k : ℕ => chartCutoff k y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«chartCutoff_mono» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_chartCutoff_mono_2f4f957da48a
