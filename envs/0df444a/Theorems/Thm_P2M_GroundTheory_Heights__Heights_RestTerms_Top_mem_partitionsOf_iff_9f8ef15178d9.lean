-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:14.871515+00:00
-- url     : https://prove2.me/theorems/2edbb898-60e5-41e1-860b-871863d999ca
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top mem partitions Of iff 9f8ef15178d9: P2 M Ground Theory Heights  Heights Rest Terms Top mem partitions Of iff 9f8ef15178d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top mem partitions Of iff 9f8ef15178d9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top mem partitions Of iff 9f8ef15178d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L126-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9 {m n : ℕ} (lam : Fin m → ℕ) :
    lam ∈ partitionsOf m n ↔ ∑ i, lam i = n ∧ Antitone lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«mem_partitionsOf_iff» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_mem_partitionsOf_iff_9f8ef15178d9
