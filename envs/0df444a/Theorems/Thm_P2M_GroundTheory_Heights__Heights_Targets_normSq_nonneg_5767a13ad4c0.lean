-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_normSq_nonneg_5767a13ad4c0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_normSq_nonneg_5767a13ad4c0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:25.834603+00:00
-- url     : https://prove2.me/theorems/05476150-bdf8-5c5b-8132-b96448ef758b
-- title:
--   P2 M Ground Theory Heights  Heights Targets norm Sq nonneg 5767a13ad4c0: P2 M Ground Theory Heights  Heights Targets norm Sq nonneg 5767a13ad4c0
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets norm Sq nonneg 5767a13ad4c0 construction uses the P2 M Ground Theory Heights  Heights Targets norm Sq nonneg 5767a13ad4c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L24-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_normSq_nonneg_5767a13ad4c0 (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : 0 ≤ normSq A s z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«normSq_nonneg» := P2M_GroundTheory_Heights__Heights_Targets_normSq_nonneg_5767a13ad4c0
