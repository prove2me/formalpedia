-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_add_8b8fd48c02c1
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_add_8b8fd48c02c1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:09.878866+00:00
-- url     : https://prove2.me/theorems/4f306bfd-63e0-4af6-ab25-80e175b52640
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing add 8b8fd48c02c1: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing add 8b8fd48c02c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing add 8b8fd48c02c1 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing add 8b8fd48c02c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L94-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L94-L101

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_add_8b8fd48c02c1 {X Y Z : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    pairing X Z s = pairing X Y s + pairing Y Z s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«pairing_add» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_add_8b8fd48c02c1
