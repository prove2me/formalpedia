-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_injective_of_good_3f4a3c80eead
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_injective_of_good_3f4a3c80eead
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:15.379894+00:00
-- url     : https://prove2.me/theorems/856ecc69-cf0e-4351-93ab-6d8aceb5c02d
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart injective of good 3f4a3c80eead: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart injective of good 3f4a3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart injective of good 3f4a3c80eead construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart injective of good 3f4a3c80eead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L114-L120

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_injective_of_good_3f4a3c80eead {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) : Function.Injective Ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«injective_of_good» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_injective_of_good_3f4a3c80eead
