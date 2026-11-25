-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_one_810125b09b0c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_one_810125b09b0c
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:48.529279+00:00
-- url     : https://prove2.me/theorems/b11698c9-f9fe-4a6f-8ec4-13efa25fb02b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise one 810125b09b0c: P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise one 810125b09b0c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise one 810125b09b0c construction uses the P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise one 810125b09b0c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L50-L56

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_one_810125b09b0c {R : Type*} [CommRing R] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (z : V → R) (hz : ∀ q, z (g q) = 1) :
    aeval z (homogenise v f g F) =
      eval₂ (aeval (z ∘ v) : MvPolynomial P ℤ →ₐ[ℤ] R).toRingHom (fun q => z (f q)) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartNormPts».«aeval_homogenise_one» := P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_one_810125b09b0c
