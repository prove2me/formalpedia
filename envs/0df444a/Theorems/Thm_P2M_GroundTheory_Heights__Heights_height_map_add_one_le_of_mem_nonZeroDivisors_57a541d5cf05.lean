-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_map_add_one_le_of_mem_nonZeroDivisors_57a541d5cf05
-- name    : P2M_GroundTheory_Heights__Heights_height_map_add_one_le_of_mem_nonZeroDivisors_57a541d5cf05
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:36.910144+00:00
-- url     : https://prove2.me/theorems/38675524-3b59-58fb-8717-bb4272d67044
-- title:
--   P2 M Ground Theory Heights  Heights height map add one le of mem non Zero Divisors 57a541d5cf05: P2 M Ground Theory Heights  Heights height map add one le of mem non Zero Divisors 57a541d5cf05
-- statement:
--   The P2 M Ground Theory Heights  Heights height map add one le of mem non Zero Divisors 57a541d5cf05 construction uses the P2 M Ground Theory Heights  Heights height map add one le of mem non Zero Divisors 57a541d5cf05 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HeightCoheightQuotient.lean#L22-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HeightCoheightQuotient.lean#L22-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights

theorem P2M_GroundTheory_Heights__Heights_height_map_add_one_le_of_mem_nonZeroDivisors_57a541d5cf05 {B : Type*} [CommRing B] [IsNoetherianRing B] {y : B}
    (hy : y ∈ nonZeroDivisors B) (P : Ideal B) [hP : P.IsPrime] (hyP : y ∈ P) :
    (P.map (Ideal.Quotient.mk (Ideal.span {y}))).height + 1 ≤ P.height := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_map_add_one_le_of_mem_nonZeroDivisors» := P2M_GroundTheory_Heights__Heights_height_map_add_one_le_of_mem_nonZeroDivisors_57a541d5cf05
