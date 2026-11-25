-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_replicate_0a9c60c52f49
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_replicate_0a9c60c52f49
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:09.918176+00:00
-- url     : https://prove2.me/theorems/2aee5d46-6846-499a-9ee2-309d5b53dd2b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff replicate 0a9c60c52f49: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff replicate 0a9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff replicate 0a9c60c52f49 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff replicate 0a9c60c52f49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L25-L29

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_replicate_0a9c60c52f49 (j : ℕ) (k : K) (g : (K → ℕ) → ℚ) :
    listDiff (List.replicate j k) g = (Δ_[(Pi.single k 1 : K → ℕ)])^[j] g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«listDiff_replicate» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_replicate_0a9c60c52f49
