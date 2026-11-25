-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_rootCoord_mul_6501e396c8a7
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_rootCoord_mul_6501e396c8a7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:17.89603+00:00
-- url     : https://prove2.me/theorems/202099a4-440f-4f11-b79d-f0eed9fa7838
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart root Coord mul 6501e396c8a7: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart root Coord mul 6501e396c8a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart root Coord mul 6501e396c8a7 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart root Coord mul 6501e396c8a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L34-L48

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_rootCoord_mul_6501e396c8a7 (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (ht : z a0 ≠ 0) :
    (fun p => rootCoord (chartPt z) p * z a0) = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«rootCoord_mul» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_rootCoord_mul_6501e396c8a7
