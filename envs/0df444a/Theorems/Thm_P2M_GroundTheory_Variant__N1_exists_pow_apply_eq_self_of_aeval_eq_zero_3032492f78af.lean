-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_pow_apply_eq_self_of_aeval_eq_zero_3032492f78af
-- name    : P2M_GroundTheory_Variant__N1_exists_pow_apply_eq_self_of_aeval_eq_zero_3032492f78af
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:47.25338+00:00
-- url     : https://prove2.me/theorems/a0e6d418-2544-4ca2-b185-fe776fc5314c
-- title:
--   P2 M Ground Theory Variant  N1 exists pow apply eq self of aeval eq zero 3032492f78af: P2 M Ground Theory Variant  N1 exists pow apply eq self of aeval eq zero 3032492f78af
-- statement:
--   The P2 M Ground Theory Variant  N1 exists pow apply eq self of aeval eq zero 3032492f78af construction uses the P2 M Ground Theory Variant  N1 exists pow apply eq self of aeval eq zero 3032492f78af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/DescentPowerSubgroups.lean#L5-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/DescentPowerSubgroups.lean#L5-L20

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_DescentPowerSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_exists_pow_apply_eq_self_of_aeval_eq_zero_3032492f78af {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (σ : Gal(Ω/K)) {p : Polynomial K} (hp : p ≠ 0) {x : Ω}
    (hx : Polynomial.aeval x p = 0) : ∃ N : ℕ, 0 < N ∧ (σ ^ N) x = x := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_pow_apply_eq_self_of_aeval_eq_zero» := P2M_GroundTheory_Variant__N1_exists_pow_apply_eq_self_of_aeval_eq_zero_3032492f78af
