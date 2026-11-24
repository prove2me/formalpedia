-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_apply_eq_segre_ad27c26f28d4
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_apply_eq_segre_ad27c26f28d4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:04.559349+00:00
-- url     : https://prove2.me/theorems/9a94715f-a0ba-49e5-a9c4-e6d5ed5271fe
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart apply eq segre ad27c26f28d4: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart apply eq segre ad27c26f28d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart apply eq segre ad27c26f28d4 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart apply eq segre ad27c26f28d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L87-L91

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_apply_eq_segre_ad27c26f28d4 (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) (p : Σ _ : Fin 1, PlIdx 1 n) :
    z p = segre (ι := plBlocks 1 1 n) z (fun _ => p.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«apply_eq_segre» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_apply_eq_segre_ad27c26f28d4
