-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_binomPoly_totalDegree_cf40ef0210b8
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_binomPoly_totalDegree_cf40ef0210b8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:34.219532+00:00
-- url     : https://prove2.me/theorems/030c7d04-ae1d-4b1a-87e8-9c62f986bc86
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial binom Poly total Degree cf40ef0210b8: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial binom Poly total Deg
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial binom Poly total Degree cf40ef0210b8 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial binom Poly total Degree cf40ef0210b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L49-L57

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_binomPoly_totalDegree_cf40ef0210b8 (c : ℕ) (k : K) (j : ℕ) : (binomPoly c k j).totalDegree ≤ j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«binomPoly_totalDegree» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_binomPoly_totalDegree_cf40ef0210b8
