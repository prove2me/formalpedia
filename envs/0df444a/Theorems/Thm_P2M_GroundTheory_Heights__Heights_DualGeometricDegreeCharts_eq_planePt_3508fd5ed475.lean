-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_eq_planePt_3508fd5ed475
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_eq_planePt_3508fd5ed475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:24.57157+00:00
-- url     : https://prove2.me/theorems/4999f41b-75b1-48d4-9e7f-084dd4b02fed
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts eq plane Pt 3508fd5ed475: P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts eq plane Pt 3508fd5ed475
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts eq plane Pt 3508fd5ed475 construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts eq plane Pt 3508fd5ed475 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L56-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L56-L73

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
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_eq_planePt_3508fd5ed475 (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    {σ : K →+* ℂ} (hσ : ∀ τ : K →+* ℂ, τ ≠ σ → ∀ j, dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) = 0) :
    z = dualPlanePt b σ (recLin b hb σ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreeCharts».«eq_planePt» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_eq_planePt_3508fd5ed475
