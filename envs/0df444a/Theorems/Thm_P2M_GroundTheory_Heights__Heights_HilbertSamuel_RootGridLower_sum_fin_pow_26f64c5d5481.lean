-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_sum_fin_pow_26f64c5d5481
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_sum_fin_pow_26f64c5d5481
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:55.348496+00:00
-- url     : https://prove2.me/theorems/0ad98bb0-7498-5ad4-899b-9cc6076cbe43
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower sum fin pow 26f64c5d5481: P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower sum fin pow 26f64c5d5481
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower sum fin pow 26f64c5d5481 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower sum fin pow 26f64c5d5481 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootGridLower.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootGridLower.lean#L9-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootGridLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootGridLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_sum_fin_pow_26f64c5d5481 {M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    {a b : ℕ} (ha : a < M) (hb : b < M) :
    ∑ t : Fin M, (ω ^ a * (ω ^ b)⁻¹) ^ (t : ℕ) = if a = b then (M : ℂ) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RootGridLower».«sum_fin_pow» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_sum_fin_pow_26f64c5d5481
