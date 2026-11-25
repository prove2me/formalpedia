-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_newton_2741b236fc44
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_newton_2741b236fc44
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:28.237372+00:00
-- url     : https://prove2.me/theorems/d55841ec-fe68-4a2c-bc31-9b9e3532d992
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial newton 2741b236fc44: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial newton 2741b236fc44
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial newton 2741b236fc44 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial newton 2741b236fc44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L70-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L70-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_newton_2741b236fc44 (c : ℕ) (s : Finset K) : ∀ (n : ℕ) (g : (K → ℕ) → ℚ),
    (∀ L : List K, L.length = n + 1 → listDiff L g = 0) →
    ∃ P : MvPolynomial K ℚ, P.totalDegree ≤ n ∧
      (∀ x y : K → ℚ, (∀ i ∈ s, x i = y i) → eval x P = eval y P) ∧
      ∀ t : K → ℕ, (∀ i ∉ s, t i = 0) → g t = eval (fun i => (t i : ℚ) + c) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«newton» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_newton_2741b236fc44
