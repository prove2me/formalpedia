-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_of_ne_zero_06f128ad0be1
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_of_ne_zero_06f128ad0be1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:42.619244+00:00
-- url     : https://prove2.me/theorems/f2fe684e-2921-4eea-b500-0b11b63ffdbd
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists of ne zero 06f128ad0be1: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists of ne zero 06f128
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists of ne zero 06f128ad0be1 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists of ne zero 06f128ad0be1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L104-L112

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_of_ne_zero_06f128ad0be1 {w : (Fin 1 → PlIdx 1 n) → ℂ} (hw : w ≠ 0) :
    blockLift (fun I => w fun _ => I) ∈ mcPts (grassIdeal 1 1 n) ∧
      segre (ι := plBlocks 1 1 n) (blockLift fun I => w fun _ => I) = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«exists_of_ne_zero» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_of_ne_zero_06f128ad0be1
