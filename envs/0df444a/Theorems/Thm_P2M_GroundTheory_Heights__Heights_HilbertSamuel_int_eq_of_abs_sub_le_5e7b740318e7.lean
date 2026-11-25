-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_int_eq_of_abs_sub_le_5e7b740318e7
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_int_eq_of_abs_sub_le_5e7b740318e7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:02.510578+00:00
-- url     : https://prove2.me/theorems/a60462b6-55dd-4106-9f91-7aca98fc1586
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel int eq of abs sub le 5e7b740318e7: P2 M Ground Theory Heights  Heights Hilbert Samuel int eq of abs sub le 5e7b740318e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel int eq of abs sub le 5e7b740318e7 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel int eq of abs sub le 5e7b740318e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L255-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L255-L269

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_int_eq_of_abs_sub_le_5e7b740318e7 {z₁ z₂ : ℤ} {c s : ℝ} (hs : 0 ≤ s) (hc : |c| < s + 1)
    (h : |(z₁ : ℝ) - (z₂ : ℝ)| ≤ c * (s + 1) ^ (((0 : ℕ) : ℝ) - 1)) : z₁ = z₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«int_eq_of_abs_sub_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_int_eq_of_abs_sub_le_5e7b740318e7
