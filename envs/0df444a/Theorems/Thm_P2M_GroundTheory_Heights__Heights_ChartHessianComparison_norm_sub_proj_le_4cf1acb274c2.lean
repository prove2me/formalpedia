-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sub_proj_le_4cf1acb274c2
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sub_proj_le_4cf1acb274c2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:43.280591+00:00
-- url     : https://prove2.me/theorems/a0b66fa0-b029-42a8-8892-bfc547e0a0de
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sub proj le 4cf1acb274c2: P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sub proj le 4cf1acb274c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sub proj le 4cf1acb274c2 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sub proj le 4cf1acb274c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L60-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L60-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sub_proj_le_4cf1acb274c2 (u D : F) (hu : u ≠ 0) (s : ℂ) :
    ‖D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u‖ ^ 2 ≤ ‖D - s • u‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«norm_sub_proj_le» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sub_proj_le_4cf1acb274c2
