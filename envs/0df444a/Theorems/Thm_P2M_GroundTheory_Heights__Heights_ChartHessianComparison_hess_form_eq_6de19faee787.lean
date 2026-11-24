-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_form_eq_6de19faee787
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_form_eq_6de19faee787
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:15.975034+00:00
-- url     : https://prove2.me/theorems/acf9ad40-720f-4466-b072-93102c5f3599
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess form eq 6de19faee787: P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess form eq 6de19faee787
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess form eq 6de19faee787 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess form eq 6de19faee787 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L176-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L176-L179

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_form_eq_6de19faee787 (hB : B.det ≠ 0) (y x : Fin e → ℂ) :
    star x ⬝ᵥ (cxHessian (hermChartPot (Bᴴ * B)) y *ᵥ x) = (hessForm B y x : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«hess_form_eq» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_form_eq_6de19faee787
