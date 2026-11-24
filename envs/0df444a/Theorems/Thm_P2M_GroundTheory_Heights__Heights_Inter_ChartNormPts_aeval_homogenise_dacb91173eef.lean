-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_dacb91173eef
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_dacb91173eef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:25.754835+00:00
-- url     : https://prove2.me/theorems/306ebd68-7959-4853-bfd9-65834b46f473
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise dacb91173eef: P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise dacb91173eef
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise dacb91173eef construction uses the P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise dacb91173eef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L31-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartNormPtsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.ChartNormPts
variable {P : Type*} {Q : Type*} [Fintype Q] {V : Type*}

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_dacb91173eef {R : Type*} [CommRing R] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (z : V → R) :
    aeval z (homogenise v f g F) =
      ∑ μ ∈ F.support, aeval (z ∘ v) (F.coeff μ) * ∏ q, z (f q) ^ μ q * z (g q) ^ (degreeOf q F - μ q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartNormPts».«aeval_homogenise» := P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_dacb91173eef
