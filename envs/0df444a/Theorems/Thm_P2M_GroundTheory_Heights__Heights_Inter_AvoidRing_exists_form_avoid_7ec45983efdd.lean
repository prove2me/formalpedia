-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_exists_form_avoid_7ec45983efdd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_exists_form_avoid_7ec45983efdd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:28.089079+00:00
-- url     : https://prove2.me/theorems/e4c147cf-7afe-4076-b946-1e79e7dc42e6
-- title:
--   P2 M Ground Theory Heights  Heights Inter Avoid Ring exists form avoid 7ec45983efdd: P2 M Ground Theory Heights  Heights Inter Avoid Ring exists form avoid 7ec45983efdd
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Avoid Ring exists form avoid 7ec45983efdd construction uses the P2 M Ground Theory Heights  Heights Inter Avoid Ring exists form avoid 7ec45983efdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L94-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/AvoidRing.lean#L94-L168

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

theorem P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_exists_form_avoid_7ec45983efdd (S : Set (Ideal (MRingOver R ι))) (hS : S.Finite)
    (hS' : ∀ W ∈ S, IsMultiProjPrime W) :
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ f : MRingOver R ι, IsMultiHomog f d ∧ ∀ W ∈ S, f ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«AvoidRing».«exists_form_avoid» := P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_exists_form_avoid_7ec45983efdd
