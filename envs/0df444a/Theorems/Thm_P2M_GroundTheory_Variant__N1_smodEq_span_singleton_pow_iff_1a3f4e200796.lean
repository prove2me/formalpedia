-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_smodEq_span_singleton_pow_iff_1a3f4e200796
-- name    : P2M_GroundTheory_Variant__N1_smodEq_span_singleton_pow_iff_1a3f4e200796
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:24:20.565045+00:00
-- url     : https://prove2.me/theorems/f82fb2d8-d161-4a0d-a40b-33258201cac3
-- title:
--   P2 M Ground Theory Variant  N1 smod Eq span singleton pow iff 1a3f4e200796: P2 M Ground Theory Variant  N1 smod Eq span singleton pow iff 1a3f4e200796
-- statement:
--   The P2 M Ground Theory Variant  N1 smod Eq span singleton pow iff 1a3f4e200796 construction uses the P2 M Ground Theory Variant  N1 smod Eq span singleton pow iff 1a3f4e200796 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PrecompleteOfSurjective.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PrecompleteOfSurjective.lean#L5-L8

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PrecompleteOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_smodEq_span_singleton_pow_iff_1a3f4e200796 {R : Type*} [CommRing R] (a : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • (⊤ : Submodule R R))] ↔ a ^ n ∣ x - y := by sorry

alias «GroundTheory».«Variant₂».«N1».«smodEq_span_singleton_pow_iff» := P2M_GroundTheory_Variant__N1_smodEq_span_singleton_pow_iff_1a3f4e200796
