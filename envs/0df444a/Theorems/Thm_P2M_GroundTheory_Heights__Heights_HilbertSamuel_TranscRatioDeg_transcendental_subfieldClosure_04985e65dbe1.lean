-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_subfieldClosure_04985e65dbe1
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_subfieldClosure_04985e65dbe1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:14:41.693811+00:00
-- url     : https://prove2.me/theorems/1dbb0ba5-9de4-5de0-b087-80f8aa6785f8
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental subfield Closure 04985e65dbe1: P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental sub
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental subfield Closure 04985e65dbe1 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental subfield Closure 04985e65dbe1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L10-L28

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_subfieldClosure_04985e65dbe1 {E : Type*} [Field E] {ι : Type*} (u : ι → E) (t : E)
    (ht : Transcendental (Algebra.adjoin ℤ (Set.range u)) t) :
    Transcendental (Subfield.closure (Set.range u)) t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«TranscRatioDeg».«transcendental_subfieldClosure» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_subfieldClosure_04985e65dbe1
