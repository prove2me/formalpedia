-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_eq_23544a1ec67b
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_eq_23544a1ec67b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:13.424719+00:00
-- url     : https://prove2.me/theorems/e3ec9f93-b7fb-4511-ae86-e28dc418ef6d
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre eq 23544a1ec67b: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre eq 23544a1ec67b
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre eq 23544a1ec67b construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart segre eq 23544a1ec67b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L83-L85

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_eq_23544a1ec67b (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (i : Fin 1 → PlIdx 1 n) :
    segre (ι := plBlocks 1 1 n) z i = z ⟨0, i 0⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«segre_eq» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_segre_eq_23544a1ec67b
