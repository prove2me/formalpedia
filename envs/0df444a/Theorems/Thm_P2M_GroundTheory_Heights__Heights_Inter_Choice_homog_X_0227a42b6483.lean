-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_X_0227a42b6483
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_X_0227a42b6483
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:42:53.16116+00:00
-- url     : https://prove2.me/theorems/5a0f4f12-a8ec-43fa-9bcf-e1985798e495
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog X 0227a42b6483: P2 M Ground Theory Heights  Heights Inter Choice homog X 0227a42b6483
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog X 0227a42b6483 construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog X 0227a42b6483 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L33-L45

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_X_0227a42b6483 (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver R ι) (Pi.single k 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_X» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_X_0227a42b6483
