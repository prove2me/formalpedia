-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_congr_b6fb4d2633eb
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_congr_b6fb4d2633eb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:15:01.282678+00:00
-- url     : https://prove2.me/theorems/274ae8f5-dc8e-43ba-abb4-458f24687e44
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin congr b6fb4d2633eb: P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin congr b6fb4d26
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin congr b6fb4d2633eb construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Transc Ratio Deg finrank adjoin congr b6fb4d2633eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L106-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LinearIndependentAdjoinOfTranscendental.lean#L106-L126

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_congr_b6fb4d2633eb {E Φ L : Type*} [Field E] [Field Φ] [Field L] [Algebra Φ E] [Algebra L E]
    {S T : Set E} (h : (algebraMap Φ E).fieldRange = (algebraMap L E).fieldRange)
    (hST : Subfield.closure (Set.range (algebraMap Φ E) ∪ S) =
      Subfield.closure (Set.range (algebraMap L E) ∪ T)) :
    Module.finrank Φ (IntermediateField.adjoin Φ S) = Module.finrank L (IntermediateField.adjoin L T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«TranscRatioDeg».«finrank_adjoin_congr» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_TranscRatioDeg_finrank_adjoin_congr_b6fb4d2633eb
