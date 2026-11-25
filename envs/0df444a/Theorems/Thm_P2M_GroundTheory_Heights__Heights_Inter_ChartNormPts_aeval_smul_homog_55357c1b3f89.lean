-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_smul_homog_55357c1b3f89
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_smul_homog_55357c1b3f89
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:41.480833+00:00
-- url     : https://prove2.me/theorems/8fde0400-ffb6-464b-b0de-feb3cd8c9c72
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval smul homog 55357c1b3f89: P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval smul homog 55357c1b3f89
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval smul homog 55357c1b3f89 construction uses the P2 M Ground Theory Heights  Heights Inter Chart Norm Pts aeval smul homog 55357c1b3f89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartNormPtsA.lean#L13-L24

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_smul_homog_55357c1b3f89 {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
    (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) (c : K → R) (z : (Σ k, ι k) → R) :
    aeval (fun p => c p.1 * z p) f = (∏ k, c k ^ a k) * aeval z f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartNormPts».«aeval_smul_homog» := P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_smul_homog_55357c1b3f89
