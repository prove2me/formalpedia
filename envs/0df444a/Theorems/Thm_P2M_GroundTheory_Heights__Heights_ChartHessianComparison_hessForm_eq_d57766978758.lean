-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_eq_d57766978758
-- name    : P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_eq_d57766978758
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:27:35.044612+00:00
-- url     : https://prove2.me/theorems/11a1843f-7c30-42fd-89de-141dc6aca1ae
-- title:
--   P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form eq d57766978758: P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form eq d57766978758
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form eq d57766978758 construction uses the P2 M Ground Theory Heights  Heights Chart Hessian Comparison hess Form eq d57766978758 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L196-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartHessCompare.lean#L196-L204

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

theorem P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_eq_d57766978758 (y x : Fin e → ℂ) :
    ∃ s : ℂ, hessForm B y x =
      (star ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y) ⬝ᵥ
          ((Bᴴ * B) *ᵥ ((Fin.cons 0 (star x) : Fin (e + 1) → ℂ) - s • Fin.cons 1 y))).re /
        (2 * (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Bᴴ * B) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartHessianComparison».«hessForm_eq» := P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_eq_d57766978758
