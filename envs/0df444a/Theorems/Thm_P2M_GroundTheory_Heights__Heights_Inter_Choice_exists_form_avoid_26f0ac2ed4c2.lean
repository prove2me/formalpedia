-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_exists_form_avoid_26f0ac2ed4c2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_exists_form_avoid_26f0ac2ed4c2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:35.359806+00:00
-- url     : https://prove2.me/theorems/705f4468-7e8a-4d09-a70d-c4c704a22513
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice exists form avoid 26f0ac2ed4c2: P2 M Ground Theory Heights  Heights Inter Choice exists form avoid 26f0ac2ed4c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice exists form avoid 26f0ac2ed4c2 construction uses the P2 M Ground Theory Heights  Heights Inter Choice exists form avoid 26f0ac2ed4c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L111-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L111-L185

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChoice
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.Choice
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_exists_form_avoid_26f0ac2ed4c2 (S : Set (Ideal (MRingOver R ι))) (hS : S.Finite)
    (hS' : ∀ W ∈ S, IsMultiProjPrime W) :
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ f : MRingOver R ι, IsMultiHomog f d ∧ ∀ W ∈ S, f ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«exists_form_avoid» := P2M_GroundTheory_Heights__Heights_Inter_Choice_exists_form_avoid_26f0ac2ed4c2
