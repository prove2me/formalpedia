-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_eq_zero_of_gradMat_2c7a0b515ee8
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_eq_zero_of_gradMat_2c7a0b515ee8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:57.764823+00:00
-- url     : https://prove2.me/theorems/713f17ed-b172-4bc0-a0eb-e3ac8f4dc219
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens eq zero of grad Mat 2c7a0b515ee8: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens eq
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens eq zero of grad Mat 2c7a0b515ee8 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens eq zero of grad Mat 2c7a0b515ee8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L140-L144

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_eq_zero_of_gradMat_2c7a0b515ee8 {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} {v w : (Fin (n + 1) → ℂ) → ℝ}
    {z : Fin (n + 1) → ℂ} (h : gradMat v w z = 0) : gradDens φ v w z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«gradDens_eq_zero_of_gradMat» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_eq_zero_of_gradMat_2c7a0b515ee8
