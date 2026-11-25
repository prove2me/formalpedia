-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_of_subfield_764aa0908cbf
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_of_subfield_764aa0908cbf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:24:06.535274+00:00
-- url     : https://prove2.me/theorems/6887ec68-dee4-52b5-9450-78d3de1930fe
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental of subfield 764aa0908cbf: P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental of subfi
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental of subfield 764aa0908cbf construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg transcendental of subfield 764aa0908cbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L30-L38

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_of_subfield_764aa0908cbf {E : Type*} [Field E] {S : Type*} [CommRing S] [Algebra S E]
    (Q : Subfield E) (h : ∀ x : S, algebraMap S E x ∈ Q) (hinj : Function.Injective (algebraMap S E))
    {t : E} (ht : Transcendental Q t) : Transcendental S t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«TranscRatioDeg».«transcendental_of_subfield» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_transcendental_of_subfield_764aa0908cbf
