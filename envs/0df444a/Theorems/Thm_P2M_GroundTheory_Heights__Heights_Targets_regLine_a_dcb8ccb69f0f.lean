-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_regLine_a_dcb8ccb69f0f
-- name    : P2M_GroundTheory_Heights__Heights_Targets_regLine_a_dcb8ccb69f0f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:33.292796+00:00
-- url     : https://prove2.me/theorems/fa367f0a-eb62-58c8-bc97-e132d6ee5747
-- title:
--   P2 M Ground Theory Heights  Heights Targets reg Line a dcb8ccb69f0f: P2 M Ground Theory Heights  Heights Targets reg Line a dcb8ccb69f0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets reg Line a dcb8ccb69f0f construction uses the P2 M Ground Theory Heights  Heights Targets reg Line a dcb8ccb69f0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L43-L44

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

theorem P2M_GroundTheory_Heights__Heights_Targets_regLine_a_dcb8ccb69f0f (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) : (regLine A s ε ha hs).a = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«regLine_a» := P2M_GroundTheory_Heights__Heights_Targets_regLine_a_dcb8ccb69f0f
