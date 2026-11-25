-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_rename_coordPow_6db4fd2d12ff
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_rename_coordPow_6db4fd2d12ff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:49.781158+00:00
-- url     : https://prove2.me/theorems/5da0b346-e75d-55f3-a468-00e82937db75
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog rename coord Pow 6db4fd2d12ff: P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog rename coord Pow 6db4fd2d12ff construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection is Multi Homog rename coord Pow 6db4fd2d12ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L73-L82

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_rename_coordPow_6db4fd2d12ff {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)) (Function.extend κ α 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardArithIntersection».«isMultiHomog_rename_coordPow» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_isMultiHomog_rename_coordPow_6db4fd2d12ff
