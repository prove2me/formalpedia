-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_blocks_posDef_595fc2157c71
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_blocks_posDef_595fc2157c71
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:51.983231+00:00
-- url     : https://prove2.me/theorems/2fc469f5-3bcc-4fd5-b34a-3ff35502144a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt blocks pos Def 595fc2157c71: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt blocks pos Def 595fc2157c71
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt blocks pos Def 595fc2157c71 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt blocks pos Def 595fc2157c71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L30-L34

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_blocks_posDef_595fc2157c71 {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hN : N.PosDef)
    (hP : P.PosDef) (i j : ℕ) (s : Fin e) : (blocks M N P i j s).PosDef := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«blocks_posDef» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_blocks_posDef_595fc2157c71
