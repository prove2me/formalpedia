-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_blockLift_a51900c6d6c2
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_blockLift_a51900c6d6c2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:11.75008+00:00
-- url     : https://prove2.me/theorems/e1757690-5d87-47c7-913b-763aad82368d
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre block Lift a51900c6d6c2: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre block Lift a51900c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre block Lift a51900c6d6c2 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre block Lift a51900c6d6c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L95-L99

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_blockLift_a51900c6d6c2 (x : PlIdx 1 n → ℂ) :
    segre (ι := plBlocks 1 1 n) (blockLift x) = fun i => x (i 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«segre_blockLift» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_blockLift_a51900c6d6c2
