-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_exists_mul_mem_of_mem_123d02d0699d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_exists_mul_mem_of_mem_123d02d0699d
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:23.9067+00:00
-- url     : https://prove2.me/theorems/cfb71bc4-8e46-4a1e-baa1-b32b91f5678b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac exists mul mem of mem 123d02d0699d: P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac exists mul mem of mem 123d02d0699d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac exists mul mem of mem 123d02d0699d construction uses the P2 M Ground Theory Heights  Heights Inter Rank Adjoin Frac exists mul mem of mem 123d02d0699d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankAdjoinFrac.lean#L31-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRankAdjoinFrac.lean#L31-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankAdjoinFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Module IntermediateField IntermediateField.algebraAdjoinAdjoin
open GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac

theorem P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_exists_mul_mem_of_mem_123d02d0699d {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) {y : Ω}
    (hy : y ∈ Algebra.adjoin (IntermediateField.adjoin F S) T) :
    ∃ a ∈ Algebra.adjoin F S, a ≠ 0 ∧ a * y ∈ Algebra.adjoin F T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RankAdjoinFrac».«exists_mul_mem_of_mem» := P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_exists_mul_mem_of_mem_123d02d0699d
