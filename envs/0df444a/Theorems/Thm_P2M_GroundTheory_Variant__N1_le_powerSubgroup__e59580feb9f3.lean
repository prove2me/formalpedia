-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_le_powerSubgroup__e59580feb9f3
-- name    : P2M_GroundTheory_Variant__N1_le_powerSubgroup__e59580feb9f3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:46.504795+00:00
-- url     : https://prove2.me/theorems/4002b45a-c0e8-530d-bf59-fb3eab502e4c
-- title:
--   P2 M Ground Theory Variant  N1 le power Subgroup  e59580feb9f3: P2 M Ground Theory Variant  N1 le power Subgroup  e59580feb9f3
-- statement:
--   The P2 M Ground Theory Variant  N1 le power Subgroup  e59580feb9f3 construction uses the P2 M Ground Theory Variant  N1 le power Subgroup  e59580feb9f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PowInvariant.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PowInvariant.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_PowInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_le_powerSubgroup__e59580feb9f3 (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    U ≤ mulZPowers U s hU := by sorry

alias «GroundTheory».«Variant₂».«N1».«le_powerSubgroup₂» := P2M_GroundTheory_Variant__N1_le_powerSubgroup__e59580feb9f3
