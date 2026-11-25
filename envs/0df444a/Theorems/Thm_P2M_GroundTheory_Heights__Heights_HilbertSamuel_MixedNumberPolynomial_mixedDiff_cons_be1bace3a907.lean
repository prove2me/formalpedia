-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_cons_be1bace3a907
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_cons_be1bace3a907
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:49.211103+00:00
-- url     : https://prove2.me/theorems/57951330-1099-47fe-bba0-4ebbf4f1c284
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff cons be1bace3a907: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff cons be1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff cons be1bace3a907 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial mixed Diff cons be1bace3a907 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L39-L41

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
variable [DecidableEq K]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_cons_be1bace3a907 {n : ℕ} (v : K → ℤ) (t : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) :
    mixedDiff (Fin.cons v t : Fin (n + 1) → K → ℤ) h = gStep v (mixedDiff t h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«mixedDiff_cons» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_cons_be1bace3a907
