-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradMat_eq_zero_left_564542ffeaa5
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradMat_eq_zero_left_564542ffeaa5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:58.633584+00:00
-- url     : https://prove2.me/theorems/af2918d2-1303-4ccc-a589-6da73ce81b16
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Mat eq zero left 564542ffeaa5: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Mat eq zero lef
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Mat eq zero left 564542ffeaa5 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Mat eq zero left 564542ffeaa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L135-L138

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradMat_eq_zero_left_564542ffeaa5 {v w : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : fderiv ℝ v z = 0) :
    gradMat v w z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«gradMat_eq_zero_left» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradMat_eq_zero_left_564542ffeaa5
