-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_inner_toLp_mulVec_9b675c86fb20
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_inner_toLp_mulVec_9b675c86fb20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:42.788618+00:00
-- url     : https://prove2.me/theorems/e24d960e-155f-4d13-8d41-e000c8c2b44f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison inner to Lp mul Vec 9b675c86fb20: P2 M Ground Theory Heights  Heights Chart Hessian Comparison inner to Lp mul Vec 9b675c86fb20
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison inner to Lp mul Vec 9b675c86fb20 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison inner to Lp mul Vec 9b675c86fb20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L136-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L136-L139

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_inner_toLp_mulVec_9b675c86fb20 (v w : Fin (e + 1) → ℂ) :
    ⟪(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))), WithLp.toLp 2 (B *ᵥ w)⟫_ℂ =
      star v ⬝ᵥ ((Bᴴ * B) *ᵥ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«inner_toLp_mulVec» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_inner_toLp_mulVec_9b675c86fb20
