-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eval_dPoly_efb5ec89d6a8
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eval_dPoly_efb5ec89d6a8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:03.385849+00:00
-- url     : https://prove2.me/theorems/d69e313f-3865-57b2-a735-98fb99322f00
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eval d Poly efb5ec89d6a8: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eval d Poly efb5ec89d6a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eval d Poly efb5ec89d6a8 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial eval d Poly efb5ec89d6a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L118-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L118-L127

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eval_dPoly_efb5ec89d6a8 (b : K → ℤ) (p : MvPolynomial K ℚ) (m : K → ℤ) :
    eval (fun k => (m k : ℚ)) (dPoly b p) =
      eval (fun k => (m k : ℚ)) p - eval (fun k => ((m - b) k : ℚ)) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«eval_dPoly» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eval_dPoly_efb5ec89d6a8
