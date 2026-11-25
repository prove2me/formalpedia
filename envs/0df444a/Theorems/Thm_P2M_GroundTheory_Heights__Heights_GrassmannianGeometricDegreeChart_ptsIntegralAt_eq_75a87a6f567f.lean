-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_ptsIntegralAt_eq_75a87a6f567f
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_ptsIntegralAt_eq_75a87a6f567f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:31.570878+00:00
-- url     : https://prove2.me/theorems/f64428e1-b0b0-4114-84c5-c93209ac7c30
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart pts Integral At eq 75a87a6f567f: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart pts Integral At eq 75a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart pts Integral At eq 75a87a6f567f construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart pts Integral At eq 75a87a6f567f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L130-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L130-L212

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_ptsIntegralAt_eq_75a87a6f567f {Ψ : (((k : Fin 1) → plBlocks 1 1 n k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hΨ : IsGoodProj (grassIdeal 1 1 n) Ψ) :
    ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
      ptsIntegralAt (grassIdeal 1 1 n) Ψ (fun _ z => Real.log ((fsMulti (plBlocks 1 1 n)).h z)) (fun _ => 1) =
        chartMass (Bᴴ * B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«ptsIntegralAt_eq» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_ptsIntegralAt_eq_75a87a6f567f
