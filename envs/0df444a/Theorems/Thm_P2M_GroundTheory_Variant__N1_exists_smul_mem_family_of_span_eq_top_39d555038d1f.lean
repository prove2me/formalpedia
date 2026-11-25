-- Prove2me | Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_smul_mem_family_of_span_eq_top_39d555038d1f
-- name    : P2M_GroundTheory_Variant__N1_exists_smul_mem_family_of_span_eq_top_39d555038d1f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:07.529238+00:00
-- url     : https://prove2.me/theorems/17bbea68-db58-4461-b483-e7cf70493ab1
-- title:
--   P2 M Ground Theory Variant  N1 exists smul mem family of span eq top 39d555038d1f: P2 M Ground Theory Variant  N1 exists smul mem family of span eq top 39d555038d1f
-- statement:
--   The P2 M Ground Theory Variant  N1 exists smul mem family of span eq top 39d555038d1f construction uses the P2 M Ground Theory Variant  N1 exists smul mem family of span eq top 39d555038d1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/ExistsSmulMemFamilyOfSpanEqTop.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/ExistsSmulMemFamilyOfSpanEqTop.lean#L41-L51

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

theorem P2M_GroundTheory_Variant__N1_exists_smul_mem_family_of_span_eq_top_39d555038d1f {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (RingOfIntegers K) (Fin N → K))
    (hM : Submodule.span K (M : Set (Fin N → K)) = ⊤)
    {ι : Type*} [Fintype ι] (v : ι → Fin N → K) :
    ∃ t : RingOfIntegers K, t ≠ 0 ∧ ∀ i, algebraMap (RingOfIntegers K) K t • v i ∈ M := by sorry

alias «GroundTheory».«Variant₂».«N1».«exists_smul_mem_family_of_span_eq_top» := P2M_GroundTheory_Variant__N1_exists_smul_mem_family_of_span_eq_top_39d555038d1f
