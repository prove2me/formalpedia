-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_pos_734925469169
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_pos_734925469169
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:39.827447+00:00
-- url     : https://prove2.me/theorems/1a984942-299b-4f62-a903-22d558858d16
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form pos 734925469169: P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form pos 734925469169
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form pos 734925469169 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form pos 734925469169 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L206-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L206-L219

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
variable {e : ℕ} (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_pos_734925469169 (hB : B.det ≠ 0) (y : Fin e → ℂ) {x : Fin e → ℂ} (hx : x ≠ 0) :
    0 < hessForm B y x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«hessForm_pos» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_pos_734925469169
