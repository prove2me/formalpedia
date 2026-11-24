-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:24.842217+00:00
-- url     : https://prove2.me/theorems/2f329dea-2eb8-4374-a3c6-7bf6f590a881
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sq to Lp mul Vec 782ab3756c0f: P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sq to Lp mul Vec 782ab3756c0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sq to Lp mul Vec 782ab3756c0f construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison norm sq to Lp mul Vec 782ab3756c0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L141-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L141-L147

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f (v : Fin (e + 1) → ℂ) :
    ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1)))‖ ^ 2 = (star v ⬝ᵥ ((Bᴴ * B) *ᵥ v)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«norm_sq_toLp_mulVec» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_norm_sq_toLp_mulVec_782ab3756c0f
