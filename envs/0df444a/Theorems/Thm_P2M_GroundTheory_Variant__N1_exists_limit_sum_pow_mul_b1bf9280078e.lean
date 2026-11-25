-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_limit_sum_pow_mul_b1bf9280078e
-- name    : P2M_GroundTheory_Variant__N1_exists_limit_sum_pow_mul_b1bf9280078e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:54.098889+00:00
-- url     : https://prove2.me/theorems/8939954e-d27e-4a69-8116-cab8b9472064
-- title:
--   P2 M Ground Theory Variant  N1 exists limit sum pow mul b1bf9280078e: P2 M Ground Theory Variant  N1 exists limit sum pow mul b1bf9280078e
-- statement:
--   The P2 M Ground Theory Variant  N1 exists limit sum pow mul b1bf9280078e construction uses the P2 M Ground Theory Variant  N1 exists limit sum pow mul b1bf9280078e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/FontainePhiPowerSubgroups.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/FontainePhiPowerSubgroups.lean#L9-L19

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_FontainePhiPowerSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_exists_limit_sum_pow_mul_b1bf9280078e {A : Type*} [CommRing A] {a : A}
    [IsPrecomplete (Ideal.span {a}) A] (b : ℕ → A) :
    ∃ L : A, ∀ n : ℕ, a ^ n ∣ (∑ k ∈ Finset.range n, a ^ k * b k) - L := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_limit_sum_pow_mul» := P2M_GroundTheory_Variant__N1_exists_limit_sum_pow_mul_b1bf9280078e
