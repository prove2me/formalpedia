-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_congr_ea53fc887cec
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_congr_ea53fc887cec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:31.678247+00:00
-- url     : https://prove2.me/theorems/9978805d-4c63-4bd3-870e-a5dde572e964
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step congr ea53fc887cec: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step cong
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step congr ea53fc887cec construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial foldr g Step congr ea53fc887cec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L228-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L228-L235

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_congr_ea53fc887cec {G : Type*} [AddCommGroup G] (l : List (K → ℤ)) {h h' : (K → ℤ) → G}
    (hh : ∀ᶠ m in atTop, h m = h' m) :
    ∀ᶠ m in atTop, l.foldr gStep h m = l.foldr gStep h' m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«foldr_gStep_congr» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_foldr_gStep_congr_ea53fc887cec
