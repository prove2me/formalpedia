-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GeoNumTarget_geoIsMultiProjPrime_9567abf63ded
-- name    : P2M_GroundTheory_Heights__Heights_GeoNumTarget_geoIsMultiProjPrime_9567abf63ded
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:11.726721+00:00
-- url     : https://prove2.me/theorems/fb38b354-8cf1-54af-a3ce-1b2b5b45dfd8
-- title:
--   P2 M Ground Theory Heights  Heights Geo Num Target geo Is Multi Proj Prime 9567abf63ded: P2 M Ground Theory Heights  Heights Geo Num Target geo Is Multi Proj Prime 9567abf63ded
-- statement:
--   The P2 M Ground Theory Heights  Heights Geo Num Target geo Is Multi Proj Prime 9567abf63ded construction uses the P2 M Ground Theory Heights  Heights Geo Num Target geo Is Multi Proj Prime 9567abf63ded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L18-L21

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

theorem P2M_GroundTheory_Heights__Heights_GeoNumTarget_geoIsMultiProjPrime_9567abf63ded {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : NumbersDVR.IsMultiProjPrime P) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GeoNumTarget».«geoIsMultiProjPrime» := P2M_GroundTheory_Heights__Heights_GeoNumTarget_geoIsMultiProjPrime_9567abf63ded
