-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_gradDens_left_c49f34d4969b
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_gradDens_left_c49f34d4969b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:38.368615+00:00
-- url     : https://prove2.me/theorems/c55329b5-8e9f-4f52-855c-2aa3ffa1ce31
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Compact Support grad Dens left c49f34d4969b: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Com
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Compact Support grad Dens left c49f34d4969b construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry has Compact Support grad Dens left c49f34d4969b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L188-L193

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_gradDens_left_c49f34d4969b {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    {v : (Fin (n + 1) → ℂ) → ℝ} (w : (Fin (n + 1) → ℂ) → ℝ) (hv : HasCompactSupport v) :
    HasCompactSupport (gradDens φ v w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«hasCompactSupport_gradDens_left» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_hasCompactSupport_gradDens_left_c49f34d4969b
