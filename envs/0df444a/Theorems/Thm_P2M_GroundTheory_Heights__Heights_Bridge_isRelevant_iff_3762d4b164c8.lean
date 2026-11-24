-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:14.630428+00:00
-- url     : https://prove2.me/theorems/4600b628-3983-44e5-8f98-d3fd3e63ff4d
-- title:
--   P2 M Ground Theory Heights  Heights Bridge is Relevant iff 3762d4b164c8: P2 M Ground Theory Heights  Heights Bridge is Relevant iff 3762d4b164c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge is Relevant iff 3762d4b164c8 construction uses the P2 M Ground Theory Heights  Heights Bridge is Relevant iff 3762d4b164c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/IsMultiHomogIdealIff.lean#L14-L15

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8 (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsRelevant W ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (R := R) W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«isRelevant_iff» := P2M_GroundTheory_Heights__Heights_Bridge_isRelevant_iff_3762d4b164c8
