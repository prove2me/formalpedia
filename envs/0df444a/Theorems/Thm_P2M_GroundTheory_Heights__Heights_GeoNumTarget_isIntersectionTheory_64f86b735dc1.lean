-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GeoNumTarget_isIntersectionTheory_64f86b735dc1
-- name    : P2M_GroundTheory_Heights__Heights_GeoNumTarget_isIntersectionTheory_64f86b735dc1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:28:48.373563+00:00
-- url     : https://prove2.me/theorems/20a11f3c-9b0a-5509-8319-16359554ed30
-- title:
--   P2 M Ground Theory Heights  Heights Geo Num Target is Intersection Theory 64f86b735dc1: P2 M Ground Theory Heights  Heights Geo Num Target is Intersection Theory 64f86b735dc1
-- statement:
--   The P2 M Ground Theory Heights  Heights Geo Num Target is Intersection Theory 64f86b735dc1 construction uses the P2 M Ground Theory Heights  Heights Geo Num Target is Intersection Theory 64f86b735dc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L37-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L37-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GeoNum
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
open GroundTheory.Heights₂.Heights.GeoNumTarget
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GeoNumTarget_isIntersectionTheory_64f86b735dc1 {F : Type} [Field F] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily F ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) :
    IsIntersectionTheory F (fun P n L => I P n L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GeoNumTarget».«isIntersectionTheory» := P2M_GroundTheory_Heights__Heights_GeoNumTarget_isIntersectionTheory_64f86b735dc1
