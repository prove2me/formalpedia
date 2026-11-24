-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:18.899205+00:00
-- url     : https://prove2.me/theorems/dd861196-99d2-4a2e-a60f-e494982dd3e5
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison to Lp mul Vec ne zero ab75d852d29d: P2 M Ground Theory Heights  Heights Chart Hessian Comparison to Lp mul Vec ne zero ab75d852d29d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison to Lp mul Vec ne zero ab75d852d29d construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison to Lp mul Vec ne zero ab75d852d29d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L149-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L149-L155

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d (hB : B.det ≠ 0) {v : Fin (e + 1) → ℂ} (hv : v ≠ 0) :
    (WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«toLp_mulVec_ne_zero» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d
