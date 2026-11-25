-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_one_9cea0c74fd23
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_one_9cea0c74fd23
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:26.236772+00:00
-- url     : https://prove2.me/theorems/e664c141-f1f8-5091-ba65-c8458316f262
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top partitions Of one 9cea0c74fd23: P2 M Ground Theory Heights  Heights Rest Terms Top partitions Of one 9cea0c74fd23
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top partitions Of one 9cea0c74fd23 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top partitions Of one 9cea0c74fd23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLinearTermValue.lean#L18-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLinearTermValue.lean#L18-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLinearTermValue
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_one_9cea0c74fd23 (r : ℕ) (hr : 1 ≤ r) : partitionsOf r 1 = {rowOne r} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«partitionsOf_one» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_partitionsOf_one_9cea0c74fd23
