-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_mixedDisc_update_sub_b6c43d3e209b
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_mixedDisc_update_sub_b6c43d3e209b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:29.702673+00:00
-- url     : https://prove2.me/theorems/1bb8d5d5-ecdd-4f20-825b-683c733c5432
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Symmetry mixed Disc update sub b6c43d3e209b: P2 M Ground Theory Heights  Heights Chart Energy Symmetry mixed Disc update sub b6c43d3e209b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Symmetry mixed Disc update sub b6c43d3e209b construction uses the P2 M Ground Theory Heights  Heights Chart Energy Symmetry mixed Disc update sub b6c43d3e209b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L36-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartIbpSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySymm
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySymmetry

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_mixedDisc_update_sub_b6c43d3e209b {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (k : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (X - Y)) =
      mixedDisc (Function.update A k X) - mixedDisc (Function.update A k Y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySymmetry».«mixedDisc_update_sub» := P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_mixedDisc_update_sub_b6c43d3e209b
