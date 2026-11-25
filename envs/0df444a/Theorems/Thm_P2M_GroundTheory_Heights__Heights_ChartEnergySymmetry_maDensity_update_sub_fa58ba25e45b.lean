-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_maDensity_update_sub_fa58ba25e45b
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_maDensity_update_sub_fa58ba25e45b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:26.994834+00:00
-- url     : https://prove2.me/theorems/4f94808c-c9e0-48b7-b33f-8e053ed8d671
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Symmetry ma Density update sub fa58ba25e45b: P2 M Ground Theory Heights  Heights Chart Energy Symmetry ma Density update sub fa58ba25e45b
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Symmetry ma Density update sub fa58ba25e45b construction uses the P2 M Ground Theory Heights  Heights Chart Energy Symmetry ma Density update sub fa58ba25e45b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L46-L55

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_maDensity_update_sub_fa58ba25e45b {D : ℕ} (Φ : Fin D → (Fin D → ℂ) → ℝ) (p : Fin D) {f g : (Fin D → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : Fin D → ℂ) :
    maDensity (Function.update Φ p f) y - maDensity (Function.update Φ p g) y =
      maDensity (Function.update Φ p fun y' => f y' - g y') y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySymmetry».«maDensity_update_sub» := P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_maDensity_update_sub_fa58ba25e45b
