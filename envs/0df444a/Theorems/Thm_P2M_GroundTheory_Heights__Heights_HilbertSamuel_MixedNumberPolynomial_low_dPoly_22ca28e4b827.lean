-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_22ca28e4b827
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_22ca28e4b827
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:41.20485+00:00
-- url     : https://prove2.me/theorems/1db44640-fcf6-4ec1-aea1-4dbe4b6e5ce8
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low d Poly 22ca28e4b827: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low d Poly 22ca28e4b827
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low d Poly 22ca28e4b827 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial low d Poly 22ca28e4b827 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L186-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L186-L194

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_22ca28e4b827 (b : K → ℤ) (p : MvPolynomial K ℚ) : Low (dPoly b p) p.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«low_dPoly» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_low_dPoly_22ca28e4b827
