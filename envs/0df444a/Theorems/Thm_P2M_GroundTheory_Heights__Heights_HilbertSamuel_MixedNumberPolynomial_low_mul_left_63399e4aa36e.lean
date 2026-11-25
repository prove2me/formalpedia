-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_mul_left_63399e4aa36e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_mul_left_63399e4aa36e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:21.127199+00:00
-- url     : https://prove2.me/theorems/d01544f5-60fc-442a-849e-e3366a328fc1
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low mul left 63399e4aa36e: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low mul left 63399e4aa3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low mul left 63399e4aa36e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low mul left 63399e4aa36e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L149-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_mul_left_63399e4aa36e {A B : MvPolynomial K ℚ} {N M : ℕ} (hB : Low B N) (hA : A.totalDegree ≤ M) :
    Low (A * B) (M + N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«low_mul_left» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_mul_left_63399e4aa36e
