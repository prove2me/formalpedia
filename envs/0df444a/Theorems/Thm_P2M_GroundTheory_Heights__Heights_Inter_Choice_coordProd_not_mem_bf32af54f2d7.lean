-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_coordProd_not_mem_bf32af54f2d7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_coordProd_not_mem_bf32af54f2d7
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:24.726662+00:00
-- url     : https://prove2.me/theorems/c466a495-389b-463e-9de5-a36ae45913f9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice coord Prod not mem bf32af54f2d7: P2 M Ground Theory Heights  Heights Inter Choice coord Prod not mem bf32af54f2d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice coord Prod not mem bf32af54f2d7 construction uses the P2 M Ground Theory Heights  Heights Inter Choice coord Prod not mem bf32af54f2d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L104-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChoice.lean#L104-L109

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_coordProd_not_mem_bf32af54f2d7 {V : Ideal (MRingOver R ι)} (hV : V.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver R ι) ∉ V) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) ∉ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«coordProd_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_Choice_coordProd_not_mem_bf32af54f2d7
