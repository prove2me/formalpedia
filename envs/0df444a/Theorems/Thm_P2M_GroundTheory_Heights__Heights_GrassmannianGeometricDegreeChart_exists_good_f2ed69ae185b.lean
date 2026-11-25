-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_good_f2ed69ae185b
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_good_f2ed69ae185b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:26.567232+00:00
-- url     : https://prove2.me/theorems/68d24cc8-2267-4c4f-8529-865678bd1196
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists good f2ed69ae185b: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists good f2ed69ae185b
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists good f2ed69ae185b construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart exists good f2ed69ae185b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L122-L128

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_good_f2ed69ae185b (n : ℕ) :
    ∃ Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj (grassIdeal 1 1 n) Ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«exists_good» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_exists_good_f2ed69ae185b
