-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_atProj_dc3d820b7c5d
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_atProj_dc3d820b7c5d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:43.369415+00:00
-- url     : https://prove2.me/theorems/243a965c-146f-4270-beef-35a3a1c63d05
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts at Proj dc3d820b7c5d: P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts at Proj dc3d820b7c5d
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts at Proj dc3d820b7c5d construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts at Proj dc3d820b7c5d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L140-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L140-L250

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

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_atProj_dc3d820b7c5d (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement)
    (hInt : ChartDensityIntegrable.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)) (hΨ : IsGoodProj (dualIdeal b) Ψ) :
    ∃ A : (K →+* ℂ) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      ptsIntegralAt (e := D) (dualIdeal b) Ψ (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) =
        ∑ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreeCharts».«atProj» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_atProj_dc3d820b7c5d
