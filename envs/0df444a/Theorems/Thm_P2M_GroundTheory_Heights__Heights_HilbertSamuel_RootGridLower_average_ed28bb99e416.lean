-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_average_ed28bb99e416
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_average_ed28bb99e416
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:49.52073+00:00
-- url     : https://prove2.me/theorems/7be7807e-0516-5395-863d-f104412abeda
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower average ed28bb99e416: P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower average ed28bb99e416
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower average ed28bb99e416 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower average ed28bb99e416 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootGridLower.lean#L30-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootGridLower.lean#L30-L66

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_average_ed28bb99e416 {e M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    (Q : MvPolynomial (Fin e) ℤ) (hdeg : ∀ i, Q.degreeOf i < M) (j : Fin e →₀ ℕ)
    (hj : ∀ i, j i < M) :
    ∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = (M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RootGridLower».«average» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_average_ed28bb99e416
