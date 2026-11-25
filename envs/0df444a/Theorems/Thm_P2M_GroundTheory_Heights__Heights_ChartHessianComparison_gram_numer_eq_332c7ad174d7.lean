-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gram_numer_eq_332c7ad174d7
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gram_numer_eq_332c7ad174d7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:11.179898+00:00
-- url     : https://prove2.me/theorems/bf75e2d9-fae8-460a-9cb1-e89e7019308f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram numer eq 332c7ad174d7: P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram numer eq 332c7ad174d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram numer eq 332c7ad174d7 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison gram numer eq 332c7ad174d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L41-L58

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gram_numer_eq_332c7ad174d7 (u D : F) (hu : u ≠ 0) :
    (⟪u, u⟫_ℂ * ⟪D, D⟫_ℂ - ⟪u, D⟫_ℂ * ⟪D, u⟫_ℂ) / (2 * ⟪u, u⟫_ℂ ^ 2) =
      ((‖D - (⟪u, D⟫_ℂ / ⟪u, u⟫_ℂ) • u‖ ^ 2 / (2 * ‖u‖ ^ 2) : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«gram_numer_eq» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_gram_numer_eq_332c7ad174d7
