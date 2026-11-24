-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:25.134229+00:00
-- url     : https://prove2.me/theorems/32646329-d67b-43dd-8ef4-514c130dcef3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog coord Prod 8cb4f1e2e87b: P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog coord Prod 8cb4f1e2e87b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog coord Prod 8cb4f1e2e87b construction uses the P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog coord Prod 8cb4f1e2e87b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L53-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L53-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter GroundTheory.Heights₂.Heights.Inter.AvoidRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«AvoidRing».«isMultiHomog_coordProd» := P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b
