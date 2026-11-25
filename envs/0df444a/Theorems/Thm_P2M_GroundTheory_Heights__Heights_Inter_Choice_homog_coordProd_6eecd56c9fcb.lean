-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_coordProd_6eecd56c9fcb
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_coordProd_6eecd56c9fcb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:49.110614+00:00
-- url     : https://prove2.me/theorems/2f34a186-6faf-4887-88f1-b3856489e6fc
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice homog coord Prod 6eecd56c9fcb: P2 M Ground Theory Heights  Heights Inter Choice homog coord Prod 6eecd56c9fcb
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice homog coord Prod 6eecd56c9fcb construction uses the P2 M Ground Theory Heights  Heights Inter Choice homog coord Prod 6eecd56c9fcb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L87-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L87-L102

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_coordProd_6eecd56c9fcb (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«homog_coordProd» := P2M_GroundTheory_Heights__Heights_Inter_Choice_homog_coordProd_6eecd56c9fcb
