-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_sum_first_pow_30fa02a376f2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_sum_first_pow_30fa02a376f2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:53.042838+00:00
-- url     : https://prove2.me/theorems/57ccc846-b798-4a01-b968-db4823bc6a8f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule sum first pow 30fa02a376f2: P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule sum first pow 30fa02a376f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule sum first pow 30fa02a376f2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule sum first pow 30fa02a376f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PShiftSumRule.lean#L32-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PShiftSumRule.lean#L32-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PShiftSumRule
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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule

theorem P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_sum_first_pow_30fa02a376f2 (r a m : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (r + a) => (i : ℕ) < a),
        (X ((0 : Fin 1), i) : RootRing 1 (r + a)) ^ m =
      blockPowerSum 1 (r + a) m 0 - smallPowerSum 1 r a .last m 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«ShiftSumRule».«sum_first_pow» := P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_sum_first_pow_30fa02a376f2
