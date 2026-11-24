-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_hermChartPot_eq_289dc0484b46
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_hermChartPot_eq_289dc0484b46
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:59.844415+00:00
-- url     : https://prove2.me/theorems/a6584cb5-640d-4be4-8d0b-49b11de7c04c
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts herm Chart Pot eq 289dc0484b46: P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts herm Chart Pot eq 289dc0484b46
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts herm Chart Pot eq 289dc0484b46 construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts herm Chart Pot eq 289dc0484b46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L92-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsDualGeomDegCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOfPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualPtsOnPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdMassAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualGeomDegCharts
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
open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.DualGeometricDegreeCharts
open StandardDualMassAtPoint
variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_hermChartPot_eq_289dc0484b46 (A h : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) (y : Fin D → ℂ) :
    hermChartPot (Aᴴ * h * A) y =
      Real.log (Real.sqrt (star (A *ᵥ Fin.cons 1 y) ⬝ᵥ (h *ᵥ (A *ᵥ Fin.cons 1 y))).re) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreeCharts».«hermChartPot_eq» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_hermChartPot_eq_289dc0484b46
