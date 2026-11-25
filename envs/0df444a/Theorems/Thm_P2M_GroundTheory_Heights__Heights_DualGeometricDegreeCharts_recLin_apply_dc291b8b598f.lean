-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_apply_dc291b8b598f
-- name    : P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_apply_dc291b8b598f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:27.082841+00:00
-- url     : https://prove2.me/theorems/5b04c2ee-5629-4923-8994-358bc259681b
-- title:
--   P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin apply dc291b8b598f: P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin apply dc291b8b598f
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin apply dc291b8b598f construction uses the P2 M Ground Theory Heights  Heights Dual Geometric Degree Charts rec Lin apply dc291b8b598f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualGeomDegCharts.lean#L40-L43

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

theorem P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_apply_dc291b8b598f (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ)
    (z : (Σ _ : Unit, T) → ℂ) (j : Fin (D + 1)) :
    recLin b hb σ z j = dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualGeometricDegreeCharts».«recLin_apply» := P2M_GroundTheory_Heights__Heights_DualGeometricDegreeCharts_recLin_apply_dc291b8b598f
