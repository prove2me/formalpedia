-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_restr_bijective_ef7ba566aeb7
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_restr_bijective_ef7ba566aeb7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:15.842632+00:00
-- url     : https://prove2.me/theorems/f09ee752-d289-43d2-8e0b-192ff66e86c2
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts restr bijective ef7ba566aeb7: P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts restr bijective ef7ba566aeb7
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts restr bijective ef7ba566aeb7 construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts restr bijective ef7ba566aeb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L129-L138

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

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_restr_bijective_ef7ba566aeb7 (hOf : DualPtsOfPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)} (hΨ : IsGoodProj (dualIdeal b) Ψ)
    (σ : K →+* ℂ) : Function.Bijective (Ψ ∘ₗ planeLin b σ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreeCharts».«restr_bijective» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_restr_bijective_ef7ba566aeb7
