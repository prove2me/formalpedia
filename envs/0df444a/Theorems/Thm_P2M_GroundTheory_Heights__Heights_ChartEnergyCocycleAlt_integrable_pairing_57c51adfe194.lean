-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_integrable_pairing_57c51adfe194
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_integrable_pairing_57c51adfe194
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:03.83681+00:00
-- url     : https://prove2.me/theorems/3b417074-07f0-4588-9c7b-4800ff1a703c
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt integrable pairing 57c51adfe194: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt integrable pairing 57c51adfe194
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt integrable pairing 57c51adfe194 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt integrable pairing 57c51adfe194 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L42-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L42-L92

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_integrable_pairing_57c51adfe194 {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    Integrable (fun y : Fin e → ℂ => (hermChartPot X y - hermChartPot Y y) * dens s y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«integrable_pairing» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_integrable_pairing_57c51adfe194
