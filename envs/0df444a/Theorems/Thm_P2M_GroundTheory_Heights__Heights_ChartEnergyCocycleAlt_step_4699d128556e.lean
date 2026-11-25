-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_step_4699d128556e
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_step_4699d128556e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:31.098828+00:00
-- url     : https://prove2.me/theorems/3b6c0656-8e93-4533-945d-333a2fb2eccd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt step 4699d128556e: P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt step 4699d128556e
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt step 4699d128556e construction uses the P2 M Ground Theory Heights  Heights Chart Energy Cocycle Alt step 4699d128556e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L120-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergyCocycle.lean#L120-L152

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_step_4699d128556e (hS : ChartEnergySymm.Statement) {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef)
    (hN : N.PosDef) (hP : P.PosDef) {k j : ℕ} (h : k + j < e) :
    pairing M N (blocks M N P k j) - pairing M N (blocks M N P k (j + 1)) =
      -(pairing N P (blocks M N P (k + 1) j) - pairing N P (blocks M N P k (j + 1))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergyCocycleAlt».«step» := P2M_GroundTheory_Heights__Heights_ChartEnergyCocycleAlt_step_4699d128556e
