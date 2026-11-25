-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_cxHessian_sub_832eb10b8be0
-- name    : P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_cxHessian_sub_832eb10b8be0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:46.711745+00:00
-- url     : https://prove2.me/theorems/01554461-1709-4823-8ec2-1792272aa667
-- title:
--   P2 M Ground Theory Heights  Heights Chart Energy Symmetry cx Hessian sub 832eb10b8be0: P2 M Ground Theory Heights  Heights Chart Energy Symmetry cx Hessian sub 832eb10b8be0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Energy Symmetry cx Hessian sub 832eb10b8be0 construction uses the P2 M Ground Theory Heights  Heights Chart Energy Symmetry cx Hessian sub 832eb10b8be0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartEnergySymm.lean#L18-L34

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

theorem P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_cxHessian_sub_832eb10b8be0 {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin D → ℂ) : cxHessian (fun y' => f y' - g y') y = cxHessian f y - cxHessian g y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartEnergySymmetry».«cxHessian_sub» := P2M_GroundTheory_Heights__Heights_ChartEnergySymmetry_cxHessian_sub_832eb10b8be0
