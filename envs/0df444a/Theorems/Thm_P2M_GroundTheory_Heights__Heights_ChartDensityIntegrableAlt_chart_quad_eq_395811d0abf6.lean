-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_chart_quad_eq_395811d0abf6
-- name    : P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_chart_quad_eq_395811d0abf6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:19:19.969043+00:00
-- url     : https://prove2.me/theorems/0a445269-e9ea-44e8-956c-89ea6cde9681
-- title:
--   P2 M Ground Theory Heights  Heights Chart Density Integrable Alt chart quad eq 395811d0abf6: P2 M Ground Theory Heights  Heights Chart Density Integrable Alt chart quad eq 395811d0abf6
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Density Integrable Alt chart quad eq 395811d0abf6 construction uses the P2 M Ground Theory Heights  Heights Chart Density Integrable Alt chart quad eq 395811d0abf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L39-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMassStA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartDensityIntegrableAlt

theorem P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_chart_quad_eq_395811d0abf6 {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hH : M.IsHermitian)
    {C : Matrix (Fin e) (Fin e) ℂ} (hNC : M.submatrix Fin.succ Fin.succ = Cᴴ * C) {d : Fin e → ℂ}
    (hd : Cᴴ *ᵥ d = fun i => M i.succ 0) (y : Fin e → ℂ) :
    star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (M 0 0 - star d ⬝ᵥ d) + star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartDensityIntegrableAlt».«chart_quad_eq» := P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_chart_quad_eq_395811d0abf6
