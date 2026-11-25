-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SameFactorBound_proof_1b71a95808a5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SameFactorBound_proof_1b71a95808a5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:53.089736+00:00
-- url     : https://prove2.me/theorems/08a100bd-8647-4682-88f7-26c63a276100
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Same Factor Bound proof 1b71a95808a5: P2 M Ground Theory Heights  Heights Rest Terms Same Factor Bound proof 1b71a95808a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Same Factor Bound proof 1b71a95808a5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Same Factor Bound proof 1b71a95808a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorBound.lean#L43-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorBound.lean#L43-L151

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorBound
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
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SameFactorBound_proof_1b71a95808a5 (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    SameFactorBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SameFactorBound».«proof» := P2M_GroundTheory_Heights__Heights_RestTerms_SameFactorBound_proof_1b71a95808a5
