-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_sum_1728fea52f29
-- name    : P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_sum_1728fea52f29
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:54.108673+00:00
-- url     : https://prove2.me/theorems/5b7c976a-cdaf-45b3-9a23-28db1c7ac8de
-- title:
--   P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog sum 1728fea52f29: P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog sum 1728fea52f29
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog sum 1728fea52f29 construction uses the P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog sum 1728fea52f29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L77-L82

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

theorem P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_sum_1728fea52f29 {β : Type*} (s : Finset β) (f : β → MRingOver R ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«AvoidRing».«isMultiHomog_sum» := P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_sum_1728fea52f29
