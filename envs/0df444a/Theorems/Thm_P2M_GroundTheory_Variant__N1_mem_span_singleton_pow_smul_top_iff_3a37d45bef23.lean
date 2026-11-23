-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_mem_span_singleton_pow_smul_top_iff_3a37d45bef23
-- name    : P2M_GroundTheory_Variant__N1_mem_span_singleton_pow_smul_top_iff_3a37d45bef23
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:00.890258+00:00
-- url     : https://prove2.me/theorems/ef767257-1cbf-45ff-8621-fcbba2dea7f4
-- title:
--   P2 M Ground Theory Variant  N1 mem span singleton pow smul top iff 3a37d45bef23: P2 M Ground Theory Variant  N1 mem span singleton pow smul top iff 3a37d45bef23
-- statement:
--   The P2 M Ground Theory Variant  N1 mem span singleton pow smul top iff 3a37d45bef23 construction uses the P2 M Ground Theory Variant  N1 mem span singleton pow smul top iff 3a37d45bef23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/FontainePhiPowerSubgroups.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/FontainePhiPowerSubgroups.lean#L5-L7

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

theorem P2M_GroundTheory_Variant__N1_mem_span_singleton_pow_smul_top_iff_3a37d45bef23 {A : Type*} [CommRing A] (a x : A) (n : ℕ) :
    x ∈ ((Ideal.span {a}) ^ n • ⊤ : Submodule A A) ↔ a ^ n ∣ x := by sorry

alias «GroundTheory».«Variant₂».«N1».«mem_span_singleton_pow_smul_top_iff» := P2M_GroundTheory_Variant__N1_mem_span_singleton_pow_smul_top_iff_3a37d45bef23
