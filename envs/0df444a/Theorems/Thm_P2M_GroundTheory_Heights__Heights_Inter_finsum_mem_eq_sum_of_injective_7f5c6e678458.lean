-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_finsum_mem_eq_sum_of_injective_7f5c6e678458
-- name    : P2M_GroundTheory_Heights__Heights_Inter_finsum_mem_eq_sum_of_injective_7f5c6e678458
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:40.307049+00:00
-- url     : https://prove2.me/theorems/12d53276-ba7a-4cff-913f-43cbc525b3b0
-- title:
--   P2 M Ground Theory Heights  Heights Inter finsum mem eq sum of injective 7f5c6e678458: P2 M Ground Theory Heights  Heights Inter finsum mem eq sum of injective 7f5c6e678458
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter finsum mem eq sum of injective 7f5c6e678458 construction uses the P2 M Ground Theory Heights  Heights Inter finsum mem eq sum of injective 7f5c6e678458 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L57-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocQuotCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter

theorem P2M_GroundTheory_Heights__Heights_Inter_finsum_mem_eq_sum_of_injective_7f5c6e678458 {α β : Type*} [Fintype β] (s : Set α) (f : α → ℝ) (g : β → α)
    (hg : Function.Injective g) (hs : ∀ x, g x ∈ s) (hf : ∀ a ∈ s, f a ≠ 0 → a ∈ Set.range g) :
    ∑ᶠ a ∈ s, f a = ∑ x, f (g x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«finsum_mem_eq_sum_of_injective» := P2M_GroundTheory_Heights__Heights_Inter_finsum_mem_eq_sum_of_injective_7f5c6e678458
