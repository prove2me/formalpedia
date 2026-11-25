-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_prod_63b54f0252db
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_prod_63b54f0252db
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:48.148801+00:00
-- url     : https://prove2.me/theorems/1bea48fd-3364-48fa-84cb-f62765cb237c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog prod 63b54f0252db: P2 M Ground Theory Heights  Heights Inter Choice homog prod 63b54f0252db
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog prod 63b54f0252db construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog prod 63b54f0252db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L77-L85

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_prod_63b54f0252db {β : Type*} (s : Finset β) (f : β → MRingOver R ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_prod» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_prod_63b54f0252db
