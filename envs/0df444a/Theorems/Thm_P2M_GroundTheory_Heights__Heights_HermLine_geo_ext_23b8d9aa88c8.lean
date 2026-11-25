-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_geo_ext_23b8d9aa88c8
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_geo_ext_23b8d9aa88c8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:07.973909+00:00
-- url     : https://prove2.me/theorems/3fa4c533-aeb7-4cac-8e51-5b393029e96f
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line geo ext 23b8d9aa88c8: P2 M Ground Theory Heights  Heights Herm Line geo ext 23b8d9aa88c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line geo ext 23b8d9aa88c8 construction uses the P2 M Ground Theory Heights  Heights Herm Line geo ext 23b8d9aa88c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L130-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.HermLine

theorem P2M_GroundTheory_Heights__Heights_HermLine_geo_ext_23b8d9aa88c8 {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
    {A B : Geo.HermLine κ} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«geo_ext» := P2M_GroundTheory_Heights__Heights_HermLine_geo_ext_23b8d9aa88c8
