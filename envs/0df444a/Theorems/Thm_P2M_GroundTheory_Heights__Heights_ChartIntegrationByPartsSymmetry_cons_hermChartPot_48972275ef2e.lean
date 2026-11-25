-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_cons_hermChartPot_48972275ef2e
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_cons_hermChartPot_48972275ef2e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:27.282888+00:00
-- url     : https://prove2.me/theorems/d460a672-c429-4aa1-ad6a-c844597933e5
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cons herm Chart Pot 48972275ef2e: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cons herm Chart Pot 48
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cons herm Chart Pot 48972275ef2e construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cons herm Chart Pot 48972275ef2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L257-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L257-L262

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_cons_hermChartPot_48972275ef2e (C : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) :
    (fun j => hermChartPot ((Fin.cons C T : Fin (n + 1) → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) j)) =
      (Fin.cons (hermChartPot C) fun i => hermChartPot (T i) : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«cons_hermChartPot» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_cons_hermChartPot_48972275ef2e
