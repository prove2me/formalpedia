-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_isLocalization_atPrime_map_d0de3ab17027
-- name    : P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_isLocalization_atPrime_map_d0de3ab17027
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:10.257941+00:00
-- url     : https://prove2.me/theorems/6f4e5fe8-e7a5-458c-b3e3-140f9ed859bc
-- title:
--   P2 M Ground Theory Heights  Heights Length Localized Localized is Localization at Prime map d0de3ab17027: P2 M Ground Theory Heights  Heights Length Localized Localized is Localization at Prime map d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Length Localized Localized is Localization at Prime map d0de3ab17027 construction uses the P2 M Ground Theory Heights  Heights Length Localized Localized is Localization at Prime map d0de3ab17027 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthLocalizedLocalized.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLengthLocalizedLocalized.lean#L9-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedLocalized
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLengthLocalizedLocalized
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

theorem P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_isLocalization_atPrime_map_d0de3ab17027 (B : Type u) [CommRing B] (P Q : Ideal B)
    [hP : P.IsPrime] [Q.IsPrime] [(P.map (algebraMap B (Localization.AtPrime Q))).IsPrime] (hPQ : P ≤ Q) :
    IsLocalization P.primeCompl (Localization.AtPrime (P.map (algebraMap B (Localization.AtPrime Q)))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LengthLocalizedLocalized».«isLocalization_atPrime_map» := P2M_GroundTheory_Heights__Heights_LengthLocalizedLocalized_isLocalization_atPrime_map_d0de3ab17027
