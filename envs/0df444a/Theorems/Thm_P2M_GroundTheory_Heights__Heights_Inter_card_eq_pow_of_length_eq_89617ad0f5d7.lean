-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_eq_pow_of_length_eq_89617ad0f5d7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_card_eq_pow_of_length_eq_89617ad0f5d7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:22:58.597815+00:00
-- url     : https://prove2.me/theorems/aa546a92-a0ee-433f-857a-630cffe695a8
-- title:
--   P2 M Ground Theory Heights  Heights Inter card eq pow of length eq 89617ad0f5d7: P2 M Ground Theory Heights  Heights Inter card eq pow of length eq 89617ad0f5d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter card eq pow of length eq 89617ad0f5d7 construction uses the P2 M Ground Theory Heights  Heights Inter card eq pow of length eq 89617ad0f5d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLength.lean#L18-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLength.lean#L18-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
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
open IsLocalRing
universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_card_eq_pow_of_length_eq_89617ad0f5d7 (n : ℕ) : ∀ (M : Type v) [AddCommGroup M] [Module R M],
    Module.length R M = n → Nat.card M = Nat.card (ResidueField R) ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«card_eq_pow_of_length_eq» := P2M_GroundTheory_Heights__Heights_Inter_card_eq_pow_of_length_eq_89617ad0f5d7
