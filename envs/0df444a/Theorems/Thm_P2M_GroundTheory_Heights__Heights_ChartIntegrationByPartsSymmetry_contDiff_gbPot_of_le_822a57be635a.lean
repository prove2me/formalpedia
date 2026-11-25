-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_gbPot_of_le_822a57be635a
-- name    : P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_gbPot_of_le_822a57be635a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:49.871464+00:00
-- url     : https://prove2.me/theorems/013e1b4f-80b7-4d58-a9d0-42cf021d5270
-- title:
--   P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff gb Pot of le 822a57be635a: P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff gb Pot of
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff gb Pot of le 822a57be635a construction uses the P2 M Ground Theory Heights  Heights Chart Integration By Parts Symmetry cont Diff gb Pot of le 822a57be635a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ChartCutoffParts.lean#L22-L26

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

theorem P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_gbPot_of_le_822a57be635a {D : ℕ} (m : ℕ) : ContDiff ℝ m (gbPot (D := D)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartIntegrationByPartsSymmetry».«contDiff_gbPot_of_le» := P2M_GroundTheory_Heights__Heights_ChartIntegrationByPartsSymmetry_contDiff_gbPot_of_le_822a57be635a
