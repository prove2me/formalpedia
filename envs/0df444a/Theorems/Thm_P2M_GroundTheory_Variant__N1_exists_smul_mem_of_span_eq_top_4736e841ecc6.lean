-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_4736e841ecc6
-- name    : P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_4736e841ecc6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:00.712673+00:00
-- url     : https://prove2.me/theorems/df29859d-89d3-4794-9d6f-7b6664f49ca6
-- title:
--   P2 M Ground Theory Variant  N1 exists smul mem of span eq top 4736e841ecc6: P2 M Ground Theory Variant  N1 exists smul mem of span eq top 4736e841ecc6
-- statement:
--   The P2 M Ground Theory Variant  N1 exists smul mem of span eq top 4736e841ecc6 construction uses the P2 M Ground Theory Variant  N1 exists smul mem of span eq top 4736e841ecc6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/ExistsSmulMemFamilyOfSpanEqTop.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/ExistsSmulMemFamilyOfSpanEqTop.lean#L7-L39

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
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

theorem P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_4736e841ecc6 {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (RingOfIntegers K) (Fin N → K))
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤) (x : Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ algebraMap (RingOfIntegers K) K t • x ∈ M := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_smul_mem_of_span_eq_top» := P2M_GroundTheory_Variant__N1_exists_smul_mem_of_span_eq_top_4736e841ecc6
