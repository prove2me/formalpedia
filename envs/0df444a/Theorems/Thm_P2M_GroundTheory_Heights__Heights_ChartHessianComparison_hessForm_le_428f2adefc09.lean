-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_le_428f2adefc09
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_le_428f2adefc09
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:26.898026+00:00
-- url     : https://prove2.me/theorems/eec94b6a-3e87-4332-898c-9cd856651e5d
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form le 428f2adefc09: P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form le 428f2adefc09
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form le 428f2adefc09 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form le 428f2adefc09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L186-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L186-L194

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_le_428f2adefc09 (hB : B.det ≠ 0) (y x : Fin e → ℂ) (s : ℂ) :
    hessForm B y x ≤
      (star ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y) ⬝ᵥ
          ((Bᴴ * B) *ᵥ ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y))).re /
        (2 * (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Bᴴ * B) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«hessForm_le» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_le_428f2adefc09
