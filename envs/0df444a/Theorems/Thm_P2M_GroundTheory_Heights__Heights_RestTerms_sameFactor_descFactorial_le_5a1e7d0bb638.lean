-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_descFactorial_le_5a1e7d0bb638
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_descFactorial_le_5a1e7d0bb638
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:36:40.970806+00:00
-- url     : https://prove2.me/theorems/fb081d2a-9062-43cc-8e64-fa0ce5b44209
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms same Factor desc Factorial le 5a1e7d0bb638: P2 M Ground Theory Heights  Heights Rest Terms same Factor desc Factorial le 5a1e7d0bb638
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms same Factor desc Factorial le 5a1e7d0bb638 construction uses the P2 M Ground Theory Heights  Heights Rest Terms same Factor desc Factorial le 5a1e7d0bb638 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorBound.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorBound.lean#L12-L28

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_descFactorial_le_5a1e7d0bb638 (n₁ N : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      (n₁ + k).descFactorial k * 2 ^ (k - 1) ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ (k - 1)
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«sameFactor_descFactorial_le» := P2M_GroundTheory_Heights__Heights_RestTerms_sameFactor_descFactorial_le_5a1e7d0bb638
