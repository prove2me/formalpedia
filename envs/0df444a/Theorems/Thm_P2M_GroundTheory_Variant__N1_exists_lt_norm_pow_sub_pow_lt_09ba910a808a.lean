-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_lt_norm_pow_sub_pow_lt_09ba910a808a
-- name    : P2M_GroundTheory_Variant__N1_exists_lt_norm_pow_sub_pow_lt_09ba910a808a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:54.815841+00:00
-- url     : https://prove2.me/theorems/5aee6b8b-458d-483c-8d24-dd8fe38a5c96
-- title:
--   P2 M Ground Theory Variant  N1 exists lt norm pow sub pow lt 09ba910a808a: P2 M Ground Theory Variant  N1 exists lt norm pow sub pow lt 09ba910a808a
-- statement:
--   The P2 M Ground Theory Variant  N1 exists lt norm pow sub pow lt 09ba910a808a construction uses the P2 M Ground Theory Variant  N1 exists lt norm pow sub pow lt 09ba910a808a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/UnramifiedClosureCountableNeighbourhoods.lean#L5-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/UnramifiedClosureCountableNeighbourhoods.lean#L5-L33

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1

theorem P2M_GroundTheory_Variant__N1_exists_lt_norm_pow_sub_pow_lt_09ba910a808a {p : ℕ} [hp : Fact (Nat.Prime p)] {c : PadicAlgCl p}
    (hc : ‖c‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) (f : ℕ → ℕ) :
    ∃ (k₀ : ℕ) (k₁ : ℕ), k₀ < k₁ ∧ ‖c ^ f k₁ - c ^ f k₀‖ < ε := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_lt_norm_pow_sub_pow_lt» := P2M_GroundTheory_Variant__N1_exists_lt_norm_pow_sub_pow_lt_09ba910a808a
