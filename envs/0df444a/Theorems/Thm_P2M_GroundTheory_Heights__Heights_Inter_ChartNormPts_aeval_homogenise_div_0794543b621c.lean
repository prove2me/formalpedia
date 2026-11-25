-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_div_0794543b621c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_div_0794543b621c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:49:26.902291+00:00
-- url     : https://prove2.me/theorems/2f6b8a6a-d354-5f39-aa34-01b07d3cba90
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise div 0794543b621c: P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise div 0794543b621c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise div 0794543b621c construction uses the P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval homogenise div 0794543b621c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L37-L48

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_div_0794543b621c {L : Type*} [Field L] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (x : V → L) (hx : ∀ q, x (g q) ≠ 0) :
    aeval x (homogenise v f g F) =
      (∏ q, x (g q) ^ degreeOf q F) *
        eval₂ (aeval (x ∘ v) : MvPolynomial P ℤ →ₐ[ℤ] L).toRingHom (fun q => x (f q) / x (g q)) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartNormPts».«aeval_homogenise_div» := P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_div_0794543b621c
