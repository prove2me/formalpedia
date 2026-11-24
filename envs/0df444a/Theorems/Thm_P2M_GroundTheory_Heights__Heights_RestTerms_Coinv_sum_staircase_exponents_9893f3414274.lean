-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_sum_staircase_exponents_9893f3414274
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_sum_staircase_exponents_9893f3414274
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:24.660443+00:00
-- url     : https://prove2.me/theorems/7649c8fb-bd0d-411d-ad1f-a6f261e3bed4
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv sum staircase exponents 9893f3414274: P2 M Ground Theory Heights  Heights Rest Terms Coinv sum staircase exponents 9893f3414274
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv sum staircase exponents 9893f3414274 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv sum staircase exponents 9893f3414274 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvStaircaseDegree.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvStaircaseDegree.lean#L9-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Coinv

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_sum_staircase_exponents_9893f3414274 (f n : ℕ) :
    ∑ v : Fin f × Fin n, (v.2 : ℕ) = coinvTop f n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«sum_staircase_exponents» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_sum_staircase_exponents_9893f3414274
