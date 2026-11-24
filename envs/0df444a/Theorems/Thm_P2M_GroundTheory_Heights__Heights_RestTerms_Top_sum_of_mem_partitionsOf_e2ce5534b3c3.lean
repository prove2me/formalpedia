-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:34.180272+00:00
-- url     : https://prove2.me/theorems/ec2abbf5-934e-44f6-b405-d611b4fd159d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top sum of mem partitions Of e2ce5534b3c3: P2 M Ground Theory Heights  Heights Rest Terms Top sum of mem partitions Of e2ce5534b3c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top sum of mem partitions Of e2ce5534b3c3 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top sum of mem partitions Of e2ce5534b3c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L283-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L283-L287

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3 {m n : ℕ} {lam : Fin m → ℕ} (h : lam ∈ partitionsOf m n) :
    ∑ i, lam i = n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«sum_of_mem_partitionsOf» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_of_mem_partitionsOf_e2ce5534b3c3
