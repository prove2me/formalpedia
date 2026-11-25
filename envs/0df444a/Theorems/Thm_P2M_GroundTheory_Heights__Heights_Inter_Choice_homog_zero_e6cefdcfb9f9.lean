-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_zero_e6cefdcfb9f9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_zero_e6cefdcfb9f9
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:24.343583+00:00
-- url     : https://prove2.me/theorems/f2f6d9fa-7249-4354-9da8-ccabe78256df
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog zero e6cefdcfb9f9: P2 M Ground Theory Heights  Heights Inter Choice homog zero e6cefdcfb9f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog zero e6cefdcfb9f9 construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog zero e6cefdcfb9f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L55-L57

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_zero_e6cefdcfb9f9 (a : K → ℕ) : IsMultiHomog (0 : MRingOver R ι) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_zero» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_zero_e6cefdcfb9f9
