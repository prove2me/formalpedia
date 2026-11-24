-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e
-- name    : P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:08.911403+00:00
-- url     : https://prove2.me/theorems/3ed1d9ee-6f34-4feb-8ae7-b44db8e899bd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Density Integrable Alt herm Chart Pot eq gb Pot affine 4211beb1f02e: P2 M Ground Theory Heights  Heights Chart Density Integrable Alt herm Chart Pot eq gb Pot
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Density Integrable Alt herm Chart Pot eq gb Pot affine 4211beb1f02e construction uses the P2 M Ground Theory Heights  Heights Chart Density Integrable Alt herm Chart Pot eq gb Pot affine 4211beb1f02e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L60-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PChartDensityIntegrable.lean#L60-L102

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

theorem P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ∃ (c : Fin e → ℂ) (P : Matrix (Fin e) (Fin e) ℂ) (κ : ℝ), P.det ≠ 0 ∧
      hermChartPot M = fun y => gbPot (c + P *ᵥ y) + κ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartDensityIntegrableAlt».«hermChartPot_eq_gbPot_affine» := P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e
