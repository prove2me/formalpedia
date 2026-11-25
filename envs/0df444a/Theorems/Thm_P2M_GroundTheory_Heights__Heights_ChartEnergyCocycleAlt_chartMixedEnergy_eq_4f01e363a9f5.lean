-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_chartMixedEnergy_eq_4f01e363a9f5
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_chartMixedEnergy_eq_4f01e363a9f5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:39.018956+00:00
-- url     : https://prove2.me/theorems/18dd9aca-ad63-40e6-a0d4-0a03609e266e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt chart Mixed Energy eq 4f01e363a9f5: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt chart Mixed Energy eq 4f01e363a9f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt chart Mixed Energy eq 4f01e363a9f5 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt chart Mixed Energy eq 4f01e363a9f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L175-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L175-L182

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyCocycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyCocycle
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyCocycleAlt
variable {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_chartMixedEnergy_eq_4f01e363a9f5 (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) :
    chartMixedEnergy X Y k = pairing X Y (fun s : Fin e => if (s : ℕ) < k then X else Y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«chartMixedEnergy_eq» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_chartMixedEnergy_eq_4f01e363a9f5
