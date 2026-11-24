-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:26.720336+00:00
-- url     : https://prove2.me/theorems/1caa48c5-5b60-4600-a4b2-1b0409ca0fd4
-- title:
--   P2 M Ground Theory Heights  Heights Bridge is Multi Homog iff c75df70a60fa: P2 M Ground Theory Heights  Heights Bridge is Multi Homog iff c75df70a60fa
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge is Multi Homog iff c75df70a60fa construction uses the P2 M Ground Theory Heights  Heights Bridge is Multi Homog iff c75df70a60fa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L42-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
variable [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa (f : NumbersDVR.MRing ι R) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«isMultiHomog_iff» := P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa
