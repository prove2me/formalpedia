-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_common_denominator_214cd264a479
-- name    : P2M_GroundTheory_Variant__N1_exists_common_denominator_214cd264a479
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:28.963585+00:00
-- url     : https://prove2.me/theorems/aa486ffb-b744-476a-8029-bbec1cee0c6f
-- title:
--   P2 M Ground Theory Variant  N1 exists common denominator 214cd264a479: P2 M Ground Theory Variant  N1 exists common denominator 214cd264a479
-- statement:
--   The P2 M Ground Theory Variant  N1 exists common denominator 214cd264a479 construction uses the P2 M Ground Theory Variant  N1 exists common denominator 214cd264a479 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/CommonDenominator.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/CommonDenominator.lean#L7-L30

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_CommonDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open NumberField

theorem P2M_GroundTheory_Variant__N1_exists_common_denominator_214cd264a479 {K : Type} [Field K] [NumberField K] {N : ℕ}
    {M : Submodule (𝓞 K) (Fin N → K)} (hM : M.FG) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ v ∈ M, ∀ i : Fin N,
      ∃ w : 𝓞 K, algebraMap (𝓞 K) K w = algebraMap (𝓞 K) K c * v i := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_common_denominator» := P2M_GroundTheory_Variant__N1_exists_common_denominator_214cd264a479
