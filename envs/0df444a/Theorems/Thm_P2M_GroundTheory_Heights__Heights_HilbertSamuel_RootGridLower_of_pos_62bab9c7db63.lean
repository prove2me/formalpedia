-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_of_pos_62bab9c7db63
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_of_pos_62bab9c7db63
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:51.627881+00:00
-- url     : https://prove2.me/theorems/af60bdd2-32c5-55ce-957b-d58e5f0e28f0
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower of pos 62bab9c7db63: P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower of pos 62bab9c7db63
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower of pos 62bab9c7db63 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Root Grid Lower of pos 62bab9c7db63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootGridLower.lean#L68-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootGridLower.lean#L68-L104

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_of_pos_62bab9c7db63 {e M : ℕ} (hM : 0 < M) (Q : MvPolynomial (Fin e) ℤ) (hQ : Q ≠ 0)
    (hdeg : ∀ i, Q.degreeOf i < M) :
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ M = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RootGridLower».«of_pos» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_of_pos_62bab9c7db63
