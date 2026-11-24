-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_cons_912e7bd7a1f6
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_cons_912e7bd7a1f6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:03.096689+00:00
-- url     : https://prove2.me/theorems/810a46a8-7b4b-45bd-b343-eeecef7dcb7e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff cons 912e7bd7a1f6: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff cons 912e7bd7a1f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff cons 912e7bd7a1f6 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff cons 912e7bd7a1f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L18-L19

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_cons_912e7bd7a1f6 (k : K) (L : List K) (g : (K → ℕ) → ℚ) (t : K → ℕ) :
    listDiff (k :: L) g t = listDiff L g (t + Pi.single k 1) - listDiff L g t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«listDiff_cons» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_cons_912e7bd7a1f6
