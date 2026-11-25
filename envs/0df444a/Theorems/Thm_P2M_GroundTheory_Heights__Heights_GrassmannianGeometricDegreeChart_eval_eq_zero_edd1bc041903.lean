-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eval_eq_zero_edd1bc041903
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eval_eq_zero_edd1bc041903
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:42.744622+00:00
-- url     : https://prove2.me/theorems/1e6c242a-f5c5-4b0c-b835-77bea0cca917
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eval eq zero edd1bc041903: P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eval eq zero edd1bc041903
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eval eq zero edd1bc041903 construction uses the P2 M Ground Theory Heights  Heights Grassmannian Geometric Degree Chart eval eq zero edd1bc041903 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L50-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean#L50-L77

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

theorem P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eval_eq_zero_edd1bc041903 {g : MRing (plBlocks 1 1 n)} (hg : g ∈ grassIdeal 1 1 n) (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) :
    MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianGeometricDegreeChart».«eval_eq_zero» := P2M_GroundTheory_Heights__Heights_GrassmannianGeometricDegreeChart_eval_eq_zero_edd1bc041903
