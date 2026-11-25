-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_map_isPrime_3f58363f6d2b
-- name    : P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_map_isPrime_3f58363f6d2b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:35.181421+00:00
-- url     : https://prove2.me/theorems/eb4f3a8c-a6a2-4ca3-a682-878099157073
-- title:
--   P2 M Ground Theory Heights  Heights Length Localized Localized map is Prime 3f58363f6d2b: P2 M Ground Theory Heights  Heights Length Localized Localized map is Prime 3f58363f6d2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Localized Localized map is Prime 3f58363f6d2b construction uses the P2 M Ground Theory Heights  Heights Length Localized Localized map is Prime 3f58363f6d2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLengthLocalizedLocalized.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLengthLocalizedLocalized.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedLocalized
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
universe u v

theorem P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_map_isPrime_3f58363f6d2b (B : Type u) [CommRing B] (P Q : Ideal B) [hP : P.IsPrime]
    [Q.IsPrime] (h : P ≤ Q) : (P.map (algebraMap B (Localization.AtPrime Q))).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthLocalizedLocalized».«map_isPrime» := P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_map_isPrime_3f58363f6d2b
