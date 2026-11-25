-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_abs_le_d574a8201a0b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_abs_le_d574a8201a0b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:42.034446+00:00
-- url     : https://prove2.me/theorems/0540d05b-8c61-4aa0-b820-148c0422744a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear abs le d574a8201a0b: P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear abs le d574a8201a0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear abs le d574a8201a0b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear abs le d574a8201a0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L89-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L89-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_abs_le_d574a8201a0b {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ m : Fin n → K → ℤ, |f m| ≤ M * ∏ i, ∑ k, |m i k| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«multilinear_abs_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_abs_le_d574a8201a0b
