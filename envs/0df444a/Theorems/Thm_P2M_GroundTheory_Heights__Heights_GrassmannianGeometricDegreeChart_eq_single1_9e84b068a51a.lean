-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eq_single1_9e84b068a51a
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eq_single1_9e84b068a51a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:22.585801+00:00
-- url     : https://prove2.me/theorems/468d75dd-4520-5a67-a0bb-7e511452bc03
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eq single1 9e84b068a51a: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eq single1 9e84b068a51a
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eq single1 9e84b068a51a construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eq single1 9e84b068a51a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L19-L24

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eq_single1_9e84b068a51a (I : PlIdx 1 n) : I = single1 (I.1.orderEmbOfFin I.2 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«eq_single1» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eq_single1_9e84b068a51a
