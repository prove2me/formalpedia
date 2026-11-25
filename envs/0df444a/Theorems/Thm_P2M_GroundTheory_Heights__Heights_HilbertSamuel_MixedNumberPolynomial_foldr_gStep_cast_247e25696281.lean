-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_cast_247e25696281
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_cast_247e25696281
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:35.424029+00:00
-- url     : https://prove2.me/theorems/cbb399e0-9ad9-5d4a-8476-baeccf77f75e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step cast 247e25696281: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step cast
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step cast 247e25696281 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step cast 247e25696281 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L219-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L219-L226

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_cast_247e25696281 (l : List (K → ℤ)) (h : (K → ℤ) → ℤ) (m : K → ℤ) :
    ((l.foldr gStep h m : ℤ) : ℚ) = l.foldr gStep (fun m => (h m : ℚ)) m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«foldr_gStep_cast» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_cast_247e25696281
