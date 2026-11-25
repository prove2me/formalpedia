-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_comm_594181c0bc9f
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_comm_594181c0bc9f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:35.913592+00:00
-- url     : https://prove2.me/theorems/7c1d4805-d010-4ca7-8fd1-4229d31cac73
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart comm 594181c0bc9f: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart comm
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart comm 594181c0bc9f construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry grad Dens chart comm 594181c0bc9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L234-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L234-L238

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_comm_594181c0bc9f {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v w : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    gradDens (fun i => hermChartPot (T i)) v w y = gradDens (fun i => hermChartPot (T i)) w v y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«gradDens_chart_comm» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_gradDens_chart_comm_594181c0bc9f
