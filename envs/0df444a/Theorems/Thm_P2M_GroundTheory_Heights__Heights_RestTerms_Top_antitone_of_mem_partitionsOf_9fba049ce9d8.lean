-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:55.642105+00:00
-- url     : https://prove2.me/theorems/ce06cb3e-7b26-4d4a-b6d6-d886fa98cc61
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top antitone of mem partitions Of 9fba049ce9d8: P2 M Ground Theory Heights  Heights Rest Terms Top antitone of mem partitions Of 9fba049ce9d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top antitone of mem partitions Of 9fba049ce9d8 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top antitone of mem partitions Of 9fba049ce9d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L278-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L278-L281

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8 {m n : ℕ} {lam : Fin m → ℕ} (h : lam ∈ partitionsOf m n) :
    Antitone lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«antitone_of_mem_partitionsOf» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_antitone_of_mem_partitionsOf_9fba049ce9d8
