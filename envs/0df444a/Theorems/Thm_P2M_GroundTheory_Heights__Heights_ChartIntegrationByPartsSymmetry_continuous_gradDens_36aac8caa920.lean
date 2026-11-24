-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_gradDens_36aac8caa920
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_gradDens_36aac8caa920
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:56.84087+00:00
-- url     : https://prove2.me/theorems/43392f58-5f1f-4584-9423-d0f909b4c9d7
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous grad Dens 36aac8caa920: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous grad Dens
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous grad Dens 36aac8caa920 construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry continuous grad Dens 36aac8caa920 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L179-L186

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_gradDens_36aac8caa920 {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    {v w : (Fin (n + 1) → ℂ) → ℝ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    Continuous (gradDens φ v w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«continuous_gradDens» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_continuous_gradDens_36aac8caa920
