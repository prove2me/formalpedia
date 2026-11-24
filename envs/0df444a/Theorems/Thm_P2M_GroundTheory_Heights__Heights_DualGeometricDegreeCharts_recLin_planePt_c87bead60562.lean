-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_planePt_c87bead60562
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_planePt_c87bead60562
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:09.020931+00:00
-- url     : https://prove2.me/theorems/2c482ede-0f43-4161-aa26-f57a53b21124
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin plane Pt c87bead60562: P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin plane Pt c87bead60562
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin plane Pt c87bead60562 construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin plane Pt c87bead60562 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L47-L52

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

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_planePt_c87bead60562 (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin (D + 1) → ℂ) :
    recLin b hb σ (dualPlanePt b σ v) = v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreeCharts».«recLin_planePt» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_planePt_c87bead60562
