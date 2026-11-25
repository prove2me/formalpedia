-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_ne_top_235876379a14
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_ne_top_235876379a14
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:45.879413+00:00
-- url     : https://prove2.me/theorems/1a90a109-968b-45d5-ad4c-a78a9a00dd2d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal ne top 235876379a14: P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal ne top 235876379a14
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal ne top 235876379a14 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal ne top 235876379a14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L80-L84

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_ne_top_235876379a14 : psumIdeal K f n ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«psumIdeal_ne_top» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_ne_top_235876379a14
