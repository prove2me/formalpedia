-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_coordPow_6706e34a9132
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_coordPow_6706e34a9132
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:42:01.828113+00:00
-- url     : https://prove2.me/theorems/785fb2ee-a7ba-40c8-af03-9a9b6b66acd9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog coord Pow 6706e34a9132: P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog coord Pow 6706e34a9132 construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog coord Pow 6706e34a9132 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L57-L69

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_coordPow_6706e34a9132 (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardArithIntersection».«isMultiHomog_coordPow» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_coordPow_6706e34a9132
