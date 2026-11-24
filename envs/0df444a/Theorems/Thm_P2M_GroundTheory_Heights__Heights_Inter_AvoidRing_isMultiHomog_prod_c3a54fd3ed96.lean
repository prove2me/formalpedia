-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_prod_c3a54fd3ed96
-- name    : P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_prod_c3a54fd3ed96
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:13.390356+00:00
-- url     : https://prove2.me/theorems/bc1ed8ac-df03-4f43-a669-1fa7e6cb4959
-- title:
--   P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog prod c3a54fd3ed96: P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog prod c3a54fd3ed96
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog prod c3a54fd3ed96 construction uses the P2 M Ground Theory Heights  Heights Inter Avoid Ring is Multi Homog prod c3a54fd3ed96 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L84-L92

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

theorem P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_prod_c3a54fd3ed96 {β : Type*} (s : Finset β) (f : β → MRingOver R ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«AvoidRing».«isMultiHomog_prod» := P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_prod_c3a54fd3ed96
