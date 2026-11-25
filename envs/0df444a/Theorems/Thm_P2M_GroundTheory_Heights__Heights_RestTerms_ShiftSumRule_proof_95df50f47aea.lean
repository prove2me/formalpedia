-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_proof_95df50f47aea
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_proof_95df50f47aea
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:02:15.677958+00:00
-- url     : https://prove2.me/theorems/922f29e4-8c53-4bb0-8773-37d4c3333cca
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule proof 95df50f47aea: P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule proof 95df50f47aea
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule proof 95df50f47aea construction uses the P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule proof 95df50f47aea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PShiftSumRule.lean#L56-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PShiftSumRule.lean#L56-L128

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
open ShiftSumRule

theorem P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_proof_95df50f47aea (hS : ShiftTotalValues.Statement)
    (h1 : FlagIntegralKillsPowerSums.Statement) : ShiftSumRule.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«ShiftSumRule».«proof» := P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_proof_95df50f47aea
