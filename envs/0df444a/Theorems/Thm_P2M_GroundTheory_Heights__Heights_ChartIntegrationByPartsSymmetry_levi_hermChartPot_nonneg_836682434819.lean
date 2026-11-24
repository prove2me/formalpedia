-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_hermChartPot_nonneg_836682434819
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_hermChartPot_nonneg_836682434819
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:53.282798+00:00
-- url     : https://prove2.me/theorems/2fa60f9c-c9a2-4099-a747-9d39f1a10be6
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi herm Chart Pot nonneg 836682434819: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi herm Chart
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi herm Chart Pot nonneg 836682434819 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry levi herm Chart Pot nonneg 836682434819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L44-L49

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
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_hermChartPot_nonneg_836682434819 {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (z ξ : Fin e → ℂ) :
    0 ≤ levi (hermChartPot M) z ξ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«levi_hermChartPot_nonneg» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_levi_hermChartPot_nonneg_836682434819
