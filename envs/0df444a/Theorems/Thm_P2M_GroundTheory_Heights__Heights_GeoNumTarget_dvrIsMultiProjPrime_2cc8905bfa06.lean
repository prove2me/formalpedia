-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GeoNumTarget_dvrIsMultiProjPrime_2cc8905bfa06
-- name    : P2M_GroundTheory_Heights__Heights_GeoNumTarget_dvrIsMultiProjPrime_2cc8905bfa06
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:18.350036+00:00
-- url     : https://prove2.me/theorems/0d61348f-2636-4643-8d5c-c96fb82bfd85
-- title:
--   P2 M Ground Theory Heights  Heights Geo Num Target dvr Is Multi Proj Prime 2cc8905bfa06: P2 M Ground Theory Heights  Heights Geo Num Target dvr Is Multi Proj Prime 2cc8905bfa06
-- statement:
--   The P2 M Ground Theory Heights  Heights Geo Num Target dvr Is Multi Proj Prime 2cc8905bfa06 construction uses the P2 M Ground Theory Heights  Heights Geo Num Target dvr Is Multi Proj Prime 2cc8905bfa06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/GeoNum.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_GeoNumTarget_dvrIsMultiProjPrime_2cc8905bfa06 {F : Type} [Field F] {P : Ideal (NumbersDVR.MRing ι F)}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P) : NumbersDVR.IsMultiProjPrime P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GeoNumTarget».«dvrIsMultiProjPrime» := P2M_GroundTheory_Heights__Heights_GeoNumTarget_dvrIsMultiProjPrime_2cc8905bfa06
