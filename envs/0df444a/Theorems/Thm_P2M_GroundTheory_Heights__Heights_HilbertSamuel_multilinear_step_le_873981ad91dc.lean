-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_le_873981ad91dc
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_le_873981ad91dc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:21.442592+00:00
-- url     : https://prove2.me/theorems/11c1dc8c-2c99-4a4a-838b-2b7bc60a1581
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step le 873981ad91dc: P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step le 873981ad91dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step le 873981ad91dc construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel multilinear step le 873981ad91dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L218-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertPrime.lean#L218-L251

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_le_873981ad91dc {d : ℕ} (f : MultilinearMap ℤ (fun _ : Fin (d + 1) => K → ℤ) ℤ)
    (hsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (m : Fin (d + 1) → K → ℤ), f (m ∘ σ) = f m) :
    ∃ M : ℤ, 0 ≤ M ∧ ∀ (a : K → ℕ) (b : K),
      |f (fun _ => fun k => (a k : ℤ)) - f (fun _ => (fun k => (a k : ℤ)) - unitDeg b) -
          ((d + 1 : ℕ) : ℤ) * f (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ))| ≤
        M * ((∑ k, (a k : ℤ)) + 1) ^ (d - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«multilinear_step_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_multilinear_step_le_873981ad91dc
