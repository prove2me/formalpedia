-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_step_add_d4bcf2015b36
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_step_add_d4bcf2015b36
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:11.308106+00:00
-- url     : https://prove2.me/theorems/c42d62e3-c9dd-58fa-8796-e3bc9015c8aa
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventual Value step add d4bcf2015b36: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventual Val
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventual Value step add d4bcf2015b36 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eventual Value step add d4bcf2015b36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L64-L75

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_step_add_d4bcf2015b36 (G : (K → ℤ) → ℤ) (x y : K → ℤ)
    (hx : ∃ c, ∀ᶠ m in atTop, gStep x G m = c) (hy : ∃ c, ∀ᶠ m in atTop, gStep y G m = c) :
    eventualValue (gStep (x + y) G) = eventualValue (gStep x G) + eventualValue (gStep y G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«eventualValue_step_add» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_step_add_d4bcf2015b36
