-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_chartCutoff_663e8ce6ba54
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_chartCutoff_663e8ce6ba54
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:00.015268+00:00
-- url     : https://prove2.me/theorems/8262b850-78f3-4109-86c0-6b147efa477b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Compact Support chart Cutoff 663e8ce6ba54: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Compa
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Compact Support chart Cutoff 663e8ce6ba54 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Compact Support chart Cutoff 663e8ce6ba54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L107-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L107-L117

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_chartCutoff_663e8ce6ba54 (k : ℕ) : HasCompactSupport (chartCutoff (D := D) k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«hasCompactSupport_chartCutoff» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_chartCutoff_663e8ce6ba54
