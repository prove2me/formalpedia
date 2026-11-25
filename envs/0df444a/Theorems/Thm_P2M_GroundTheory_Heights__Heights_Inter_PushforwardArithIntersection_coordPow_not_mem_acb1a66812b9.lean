-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_coordPow_not_mem_acb1a66812b9
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_coordPow_not_mem_acb1a66812b9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:42:06.4688+00:00
-- url     : https://prove2.me/theorems/8ccd0883-b39f-4a21-bf92-1bb86cfe5b57
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection coord Pow not mem acb1a66812b9: P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection coord Pow not mem acb1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection coord Pow not mem acb1a66812b9 construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection coord Pow not mem acb1a66812b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L86-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_coordPow_not_mem_acb1a66812b9 {V : Ideal (MRing ι)} (hV : V.IsPrime) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ V) (α : K → ℕ) : (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardArithIntersection».«coordPow_not_mem» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_coordPow_not_mem_acb1a66812b9
