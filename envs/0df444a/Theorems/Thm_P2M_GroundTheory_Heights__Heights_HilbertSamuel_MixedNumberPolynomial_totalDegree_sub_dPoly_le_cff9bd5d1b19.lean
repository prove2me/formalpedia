-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_totalDegree_sub_dPoly_le_cff9bd5d1b19
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_totalDegree_sub_dPoly_le_cff9bd5d1b19
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:21.984912+00:00
-- url     : https://prove2.me/theorems/c3993c32-f739-5716-8dc3-f44b6ea2941c
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial total Degree sub d Poly le cff9bd5d1b19: P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial total Deg
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial total Degree sub d Poly le cff9bd5d1b19 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Mixed Number Polynomial total Degree sub d Poly le cff9bd5d1b19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMixedNumberPolynomial.lean#L159-L164

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_totalDegree_sub_dPoly_le_cff9bd5d1b19 {b : K → ℤ} {A : MvPolynomial K ℚ} {N : ℕ}
    (hd : A.totalDegree ≤ N) (hl : Low (dPoly b A) N) : (A - dPoly b A).totalDegree ≤ N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MixedNumberPolynomial».«totalDegree_sub_dPoly_le» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_totalDegree_sub_dPoly_le_cff9bd5d1b19
