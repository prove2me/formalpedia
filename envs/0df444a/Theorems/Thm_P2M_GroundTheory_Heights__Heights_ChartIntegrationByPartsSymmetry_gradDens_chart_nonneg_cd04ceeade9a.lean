-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_nonneg_cd04ceeade9a
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_nonneg_cd04ceeade9a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:54.206319+00:00
-- url     : https://prove2.me/theorems/0fd87880-b3b8-42d7-a46c-80805d7155dd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart nonneg cd04ceeade9a: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart non
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart nonneg cd04ceeade9a construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart nonneg cd04ceeade9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L240-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L240-L244

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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_nonneg_cd04ceeade9a {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    0 ≤ gradDens (fun i => hermChartPot (T i)) v v y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«gradDens_chart_nonneg» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_nonneg_cd04ceeade9a
