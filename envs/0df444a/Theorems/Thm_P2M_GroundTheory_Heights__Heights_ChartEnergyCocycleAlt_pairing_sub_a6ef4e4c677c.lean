-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_sub_a6ef4e4c677c
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_sub_a6ef4e4c677c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:58.920803+00:00
-- url     : https://prove2.me/theorems/0e55614d-3bc6-4224-9cc1-f456b045ab60
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing sub a6ef4e4c677c: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing sub a6ef4e4c677c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing sub a6ef4e4c677c construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing sub a6ef4e4c677c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L103-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L103-L110

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_sub_a6ef4e4c677c {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s t : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) (ht : ∀ j, (t j).PosDef) :
    pairing X Y s - pairing X Y t = ∫ y, (hermChartPot X y - hermChartPot Y y) * (dens s y - dens t y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«pairing_sub» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_sub_a6ef4e4c677c
