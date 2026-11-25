-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_alt_1fef0ba5d336
-- name    : P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_alt_1fef0ba5d336
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:06.022487+00:00
-- url     : https://prove2.me/theorems/e6a9b81e-24d4-48b7-8239-34014a31b148
-- title:
--   P2 M Ground Theory Variant  N1 exists smul mem of span eq top alt 1fef0ba5d336: P2 M Ground Theory Variant  N1 exists smul mem of span eq top alt 1fef0ba5d336
-- statement:
--   The P2 M Ground Theory Variant  N1 exists smul mem of span eq top alt 1fef0ba5d336 construction uses the P2 M Ground Theory Variant  N1 exists smul mem of span eq top alt 1fef0ba5d336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/SpanEqTopSmul.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/SpanEqTopSmul.lean#L7-L35

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_SpanEqTopSmul
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

theorem P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_alt_1fef0ba5d336 {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (Λ : Submodule (𝓞 K) (Fin n → K))
    (hΛ : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (v : Fin n → K) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Λ := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_smul_mem_of_span_eq_top_alt» := P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_alt_1fef0ba5d336
