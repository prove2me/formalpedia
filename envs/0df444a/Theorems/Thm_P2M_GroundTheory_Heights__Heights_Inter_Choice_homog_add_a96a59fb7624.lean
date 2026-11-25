-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_add_a96a59fb7624
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_add_a96a59fb7624
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:21.165735+00:00
-- url     : https://prove2.me/theorems/abb27c60-2f0c-455a-87d7-74c8c0fbb780
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog add a96a59fb7624: P2 M Ground Theory Heights  Heights Inter Choice homog add a96a59fb7624
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog add a96a59fb7624 construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog add a96a59fb7624 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L59-L65

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_add_a96a59fb7624 {f g : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_add» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_add_a96a59fb7624
