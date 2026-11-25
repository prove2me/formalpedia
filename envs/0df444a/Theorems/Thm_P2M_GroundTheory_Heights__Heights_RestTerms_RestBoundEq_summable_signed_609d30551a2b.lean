-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_summable_signed_609d30551a2b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_summable_signed_609d30551a2b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:59.124479+00:00
-- url     : https://prove2.me/theorems/ad6341fc-fd1f-4353-a6d6-1f6f6746b717
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq summable signed 609d30551a2b: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq summable signed 609d30551a2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq summable signed 609d30551a2b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq summable signed 609d30551a2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealTransferOfSyzygy.lean#L13-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy
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
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_summable_signed_609d30551a2b (p : ℕ) (hp : 2 ≤ p) (k : ℕ) (hk : 1 ≤ k) (R : ℚ) (ε : ℕ → ℚ)
    (hε : ∀ n, ε n = 1 ∨ ε n = -1) :
    Summable (fun n : ℕ => ((p : ℝ) ^ ((n + 1) * k))⁻¹ * ((ε n * R : ℚ) : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«summable_signed» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_summable_signed_609d30551a2b
