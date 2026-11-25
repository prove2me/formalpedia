-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_eval_binomPoly_aa54a0e3201d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_eval_binomPoly_aa54a0e3201d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:28.996796+00:00
-- url     : https://prove2.me/theorems/7e69f6d6-2aad-4f7c-ba0e-ffd0c908b1d9
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial eval binom Poly aa54a0e3201d: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial eval binom Poly aa54a0e3201d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial eval binom Poly aa54a0e3201d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial eval binom Poly aa54a0e3201d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L60-L68

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
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_eval_binomPoly_aa54a0e3201d (c : ℕ) (k : K) (j : ℕ) (x : K → ℚ) (m : ℕ) (hx : x k = (m : ℚ) + c) :
    eval x (binomPoly c k j) = (m.choose j : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«eval_binomPoly» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_eval_binomPoly_aa54a0e3201d
