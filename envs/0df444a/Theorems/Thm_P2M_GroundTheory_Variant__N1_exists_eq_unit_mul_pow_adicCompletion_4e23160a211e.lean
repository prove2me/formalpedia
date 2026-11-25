-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_eq_unit_mul_pow_adicCompletion_4e23160a211e
-- name    : P2M_GroundTheory_Variant__N1_exists_eq_unit_mul_pow_adicCompletion_4e23160a211e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:57.81402+00:00
-- url     : https://prove2.me/theorems/e4917196-d751-4e4c-a870-a073afe2c78c
-- title:
--   P2 M Ground Theory Variant  N1 exists eq unit mul pow adic Completion 4e23160a211e: P2 M Ground Theory Variant  N1 exists eq unit mul pow adic Completion 4e23160a211e
-- statement:
--   The P2 M Ground Theory Variant  N1 exists eq unit mul pow adic Completion 4e23160a211e construction uses the P2 M Ground Theory Variant  N1 exists eq unit mul pow adic Completion 4e23160a211e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/UnitMulPowAdic.lean#L7-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/UnitMulPowAdic.lean#L7-L53

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open IsLocalRing

theorem P2M_GroundTheory_Variant__N1_exists_eq_unit_mul_pow_adicCompletion_4e23160a211e {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : AdicCompletion (maximalIdeal R) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (maximalIdeal R) R)ˣ),
      x = ↑u * (algebraMap R (AdicCompletion (maximalIdeal R) R)) ϖ ^ n := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_eq_unit_mul_pow_adicCompletion» := P2M_GroundTheory_Variant__N1_exists_eq_unit_mul_pow_adicCompletion_4e23160a211e
