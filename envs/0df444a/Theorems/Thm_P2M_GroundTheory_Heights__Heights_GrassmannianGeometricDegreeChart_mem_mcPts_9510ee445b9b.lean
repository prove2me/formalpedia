-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_mem_mcPts_9510ee445b9b
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_mem_mcPts_9510ee445b9b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:50.566825+00:00
-- url     : https://prove2.me/theorems/3ebb8f28-d150-4e0c-b4f3-d97fe95f678e
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart mem mc Pts 9510ee445b9b: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart mem mc Pts 9510ee445b9b
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart mem mc Pts 9510ee445b9b construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart mem mc Pts 9510ee445b9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L79-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.GrassmannianGeometricDegreeChart
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_mem_mcPts_9510ee445b9b (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    z ∈ mcPts (grassIdeal 1 1 n) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«mem_mcPts» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_mem_mcPts_9510ee445b9b
