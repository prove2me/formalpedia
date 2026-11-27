-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_mem_mulZPowers_self_ff64b1724fe2
-- name    : P2M_GroundTheory_Variant__N1_mem_mulZPowers_self_ff64b1724fe2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:44.696143+00:00
-- url     : https://prove2.me/theorems/fd9d4df9-8b4c-55f8-ad61-34f89776d452
-- title:
--   P2 M Ground Theory Variant  N1 mem mul ZPowers self ff64b1724fe2: P2 M Ground Theory Variant  N1 mem mul ZPowers self ff64b1724fe2
-- statement:
--   The P2 M Ground Theory Variant  N1 mem mul ZPowers self ff64b1724fe2 construction uses the P2 M Ground Theory Variant  N1 mem mul ZPowers self ff64b1724fe2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PowInvariant.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/PowInvariant.lean#L25-L27

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

theorem P2M_GroundTheory_Variant__N1_mem_mulZPowers_self_ff64b1724fe2 (U : Subgroup Gal(AlgebraicClosure ℚ/ℚ))
    (s : Gal(AlgebraicClosure ℚ/ℚ)) (hU : ∀ (k : ℤ), ∀ x ∈ U, s ^ k * x * (s ^ k)⁻¹ ∈ U) :
    s ∈ mulZPowers U s hU := by sorry

alias «GroundTheory».«Variant₂».«N1».«mem_mulZPowers_self» := P2M_GroundTheory_Variant__N1_mem_mulZPowers_self_ff64b1724fe2
