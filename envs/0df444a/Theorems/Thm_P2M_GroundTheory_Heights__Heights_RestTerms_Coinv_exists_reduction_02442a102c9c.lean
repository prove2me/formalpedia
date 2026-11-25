-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_exists_reduction_02442a102c9c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_exists_reduction_02442a102c9c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:31.4988+00:00
-- url     : https://prove2.me/theorems/faac35f4-4ff2-469b-991d-1c9d34cac775
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv exists reduction 02442a102c9c: P2 M Ground Theory Heights  Heights Rest Terms Coinv exists reduction 02442a102c9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv exists reduction 02442a102c9c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv exists reduction 02442a102c9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L86-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L86-L161

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}
variable [CharZero K]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_exists_reduction_02442a102c9c (b : Fin f) (k : Fin n) :
    ∃ c : ℕ → MvPolynomial ↥(Finset.Ioi k) K,
      X (b, k) ^ ((k : ℕ) + 1) + ∑ j ∈ range ((k : ℕ) + 1),
        rename (fun s : ↥(Finset.Ioi k) => (b, (s : Fin n))) (c j) * X (b, k) ^ j ∈
        psumIdeal K f n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«exists_reduction» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_exists_reduction_02442a102c9c
