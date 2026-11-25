-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_update_posDef_4a4c0cf250d1
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_update_posDef_4a4c0cf250d1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:23:24.473772+00:00
-- url     : https://prove2.me/theorems/f21fd22e-b5f8-4c54-b777-841e08b348c9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt update pos Def 4a4c0cf250d1: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt update pos Def 4a4c0cf250d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt update pos Def 4a4c0cf250d1 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt update pos Def 4a4c0cf250d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L36-L40

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_update_posDef_4a4c0cf250d1 {T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hT : ∀ j, (T j).PosDef) (p : Fin e)
    {X : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (s : Fin e) : (Function.update T p X s).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«update_posDef» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_update_posDef_4a4c0cf250d1
