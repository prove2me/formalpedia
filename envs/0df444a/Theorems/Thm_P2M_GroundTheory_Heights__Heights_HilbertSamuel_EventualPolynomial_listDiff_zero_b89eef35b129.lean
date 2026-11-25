-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_zero_b89eef35b129
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_zero_b89eef35b129
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:26.056541+00:00
-- url     : https://prove2.me/theorems/a2293a43-ea07-41cb-ae6c-d06ad9a60eff
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff zero b89eef35b129: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff zero b89eef35b129
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff zero b89eef35b129 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff zero b89eef35b129 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L31-L37

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_zero_b89eef35b129 (L : List K) : listDiff L (0 : (K → ℕ) → ℚ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«listDiff_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_zero_b89eef35b129
