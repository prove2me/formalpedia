-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_pow_fbfa36c014cc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_pow_fbfa36c014cc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:22:48.306185+00:00
-- url     : https://prove2.me/theorems/57dcfafb-5acf-4ae3-93c6-fabf41ccbd32
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog pow fbfa36c014cc: P2 M Ground Theory Heights  Heights Inter Choice homog pow fbfa36c014cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog pow fbfa36c014cc construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog pow fbfa36c014cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L47-L53

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_pow_fbfa36c014cc {f : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_pow» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_pow_fbfa36c014cc
