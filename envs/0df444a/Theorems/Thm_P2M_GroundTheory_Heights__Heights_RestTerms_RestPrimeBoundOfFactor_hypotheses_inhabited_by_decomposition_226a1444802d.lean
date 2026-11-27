-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestPrimeBoundOfFactor_hypotheses_inhabited_by_decomposition_226a1444802d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestPrimeBoundOfFactor_hypotheses_inhabited_by_decomposition_226a1444802d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:36:48.525857+00:00
-- url     : https://prove2.me/theorems/c7a09780-0439-4856-9e09-cef7ea2ab3f7
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Prime Bound Of Factor hypotheses inhabited by decomposition 226a1444802d: P2 M Ground Theory Heights  Heights Rest Terms Rest Prime Bound Of Factor
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Prime Bound Of Factor hypotheses inhabited by decomposition 226a1444802d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Prime Bound Of Factor hypotheses inhabited by decomposition 226a1444802d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsElem.lean#L44-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestPrimeBoundOfFactor_hypotheses_inhabited_by_decomposition_226a1444802d :
    IsPowerSumDecomposition 1 (1 + 1) (restPolynomial 1 1 1 .last) inhQ ∧
    restTerm 1 (1 + 1) inhQ 2 0 (smallPowerSum 1 1 1 .last (2 - 1) 0) ≠ 0 ∧
    ∀ k : ℕ, 2 ≤ k → k ≤ 1 + 1 → ∀ τ τ' : Fin 1,
        |restTerm 1 (1 + 1) inhQ k τ (smallPowerSum 1 1 1 .last (k - 1) τ')| ≤
          ((1 * (1 * 1) + 1 : ℕ) : ℚ) * |fibreDegree 1 1 1 .last| * restX 1 1 ^ (k - 1) /
            (k.factorial : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestPrimeBoundOfFactor».«hypotheses_inhabited_by_decomposition» := P2M_GroundTheory_Heights__Heights_RestTerms_RestPrimeBoundOfFactor_hypotheses_inhabited_by_decomposition_226a1444802d
