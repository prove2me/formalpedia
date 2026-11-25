-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_contDiff_evalC_435b0b7923c5
-- name    : P2M_GroundTheory_Heights__Heights_Targets_contDiff_evalC_435b0b7923c5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:28.453459+00:00
-- url     : https://prove2.me/theorems/2f555b94-5b00-42ec-8519-95779fa69ce5
-- title:
--   P2 M Ground Theory Heights  Heights Targets cont Diff eval C 435b0b7923c5: P2 M Ground Theory Heights  Heights Targets cont Diff eval C 435b0b7923c5
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets cont Diff eval C 435b0b7923c5 construction uses the P2 M Ground Theory Heights  Heights Targets cont Diff eval C 435b0b7923c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L51-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/IsMultiHomogPlaneCoordinate.lean#L51-L57

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

theorem P2M_GroundTheory_Heights__Heights_Targets_contDiff_evalC_435b0b7923c5 (s : MRing ι) :
    ContDiff ℝ ∞ (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) s)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«contDiff_evalC» := P2M_GroundTheory_Heights__Heights_Targets_contDiff_evalC_435b0b7923c5
