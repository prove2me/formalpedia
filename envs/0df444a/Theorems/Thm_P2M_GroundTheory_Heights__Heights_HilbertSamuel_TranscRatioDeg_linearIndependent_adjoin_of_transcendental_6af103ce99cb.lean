-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_linearIndependent_adjoin_of_transcendental_6af103ce99cb
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_linearIndependent_adjoin_of_transcendental_6af103ce99cb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:43.254799+00:00
-- url     : https://prove2.me/theorems/282e4a45-6ad8-49ee-ad89-d75566ebe5d2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg linear Independent adjoin of transcendental 6af103ce99cb: P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg linear
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg linear Independent adjoin of transcendental 6af103ce99cb construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg linear Independent adjoin of transcendental 6af103ce99cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L42-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L42-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LinearIndependentAdjoinOfTranscendental
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
open GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_linearIndependent_adjoin_of_transcendental_6af103ce99cb {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) {κ : Type*} {b : κ → A}
    (hb : LinearIndependent K b) :
    LinearIndependent (IntermediateField.adjoin K {t}) (A.val ∘ b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«TranscRatioDeg».«linearIndependent_adjoin_of_transcendental» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_linearIndependent_adjoin_of_transcendental_6af103ce99cb
