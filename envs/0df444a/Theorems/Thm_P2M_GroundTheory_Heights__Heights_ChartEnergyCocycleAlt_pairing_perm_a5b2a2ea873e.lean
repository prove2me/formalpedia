-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_perm_a5b2a2ea873e
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_perm_a5b2a2ea873e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:59.525749+00:00
-- url     : https://prove2.me/theorems/1b1e4b8b-e780-4218-baf3-10fa6e69d477
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing perm a5b2a2ea873e: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing perm a5b2a2ea873e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing perm a5b2a2ea873e construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt pairing perm a5b2a2ea873e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L112-L118

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_perm_a5b2a2ea873e (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (σ : Equiv.Perm (Fin e)) : pairing X Y (s ∘ σ) = pairing X Y s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«pairing_perm» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_pairing_perm_a5b2a2ea873e
