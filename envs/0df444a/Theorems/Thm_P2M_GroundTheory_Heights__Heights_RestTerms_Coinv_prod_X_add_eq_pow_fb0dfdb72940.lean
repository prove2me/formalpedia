-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_prod_X_add_eq_pow_fb0dfdb72940
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_prod_X_add_eq_pow_fb0dfdb72940
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:34.384565+00:00
-- url     : https://prove2.me/theorems/fb8c3c49-1b75-4bdb-b10b-93fc8336cb1b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv prod X add eq pow fb0dfdb72940: P2 M Ground Theory Heights  Heights Rest Terms Coinv prod X add eq pow fb0dfdb72940
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv prod X add eq pow fb0dfdb72940 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv prod X add eq pow fb0dfdb72940 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L49-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L49-L70

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_prod_X_add_eq_pow_fb0dfdb72940 (b : Fin f) :
    (∏ i : Fin n, (Polynomial.X + Polynomial.C
      (Ideal.Quotient.mk (psumIdeal K f n) (X (b, i))))) = Polynomial.X ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«prod_X_add_eq_pow» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_prod_X_add_eq_pow_fb0dfdb72940
