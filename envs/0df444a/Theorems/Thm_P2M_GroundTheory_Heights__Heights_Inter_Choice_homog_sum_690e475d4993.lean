-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_sum_690e475d4993
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_sum_690e475d4993
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:51.468804+00:00
-- url     : https://prove2.me/theorems/3b44a0eb-17d7-4530-997e-1f4089e88347
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog sum 690e475d4993: P2 M Ground Theory Heights  Heights Inter Choice homog sum 690e475d4993
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog sum 690e475d4993 construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog sum 690e475d4993 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L67-L75

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_sum_690e475d4993 {β : Type*} (s : Finset β) (f : β → MRingOver R ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_sum» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_sum_690e475d4993
