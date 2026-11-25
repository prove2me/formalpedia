-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_eq_of_transcendental_e239a4901d9a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_eq_of_transcendental_e239a4901d9a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:14:44.580281+00:00
-- url     : https://prove2.me/theorems/6b9c86fa-8c74-58ef-926f-e834b47ec505
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin eq of transcendental e239a4901d9a: P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin eq of transcendental e239a4901d9a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin eq of transcendental e239a4901d9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L83-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L83-L104

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_eq_of_transcendental_e239a4901d9a {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) :
    Module.finrank (IntermediateField.adjoin K {t})
      (IntermediateField.adjoin (IntermediateField.adjoin K {t}) (A : Set E)) = Module.finrank K A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«TranscRatioDeg».«finrank_adjoin_eq_of_transcendental» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_eq_of_transcendental_e239a4901d9a
