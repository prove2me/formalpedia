-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_le_ker_3e0fba5eabdb
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_le_ker_3e0fba5eabdb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:47.697802+00:00
-- url     : https://prove2.me/theorems/5a1a453d-49b5-4f5e-adea-dd4be6a25740
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal le ker 3e0fba5eabdb: P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal le ker 3e0fba5eabdb
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal le ker 3e0fba5eabdb construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv psum Ideal le ker 3e0fba5eabdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L74-L78

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
variable (K)
omit [CharZero K]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_le_ker_3e0fba5eabdb :
    psumIdeal K f n ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin f × Fin n) K →+* K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«psumIdeal_le_ker» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_le_ker_3e0fba5eabdb
