-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_psum_aae3244de93b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_psum_aae3244de93b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:41.338314+00:00
-- url     : https://prove2.me/theorems/fcf45889-280d-4fc2-a841-d2502e38191d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv rename psum aae3244de93b: P2 M Ground Theory Heights  Heights Rest Terms Coinv rename psum aae3244de93b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv rename psum aae3244de93b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv rename psum aae3244de93b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_psum_aae3244de93b (b : Fin f) (m : ℕ) :
    rename (fun i : Fin n => (b, i)) (psum (Fin n) K m) = bps K f n m b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«rename_psum» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_psum_aae3244de93b
