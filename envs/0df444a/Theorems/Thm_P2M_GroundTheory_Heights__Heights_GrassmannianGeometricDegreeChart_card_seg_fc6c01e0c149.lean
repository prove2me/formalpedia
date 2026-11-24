-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_card_seg_fc6c01e0c149
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_card_seg_fc6c01e0c149
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:00.962803+00:00
-- url     : https://prove2.me/theorems/9f2f49a4-0dbb-4025-9e4c-828d27f8af2f
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart card seg fc6c01e0c149: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart card seg fc6c01e0c149
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart card seg fc6c01e0c149 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart card seg fc6c01e0c149 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L101-L102

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_card_seg_fc6c01e0c149 : Fintype.card (Fin 1 → PlIdx 1 n) = n + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«card_seg» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_card_seg_fc6c01e0c149
