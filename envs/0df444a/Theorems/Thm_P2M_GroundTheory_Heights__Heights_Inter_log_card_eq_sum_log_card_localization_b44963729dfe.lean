-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_eq_sum_log_card_localization_b44963729dfe
-- name    : P2M_GroundTheory_Heights__Heights_Inter_log_card_eq_sum_log_card_localization_b44963729dfe
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:44.012846+00:00
-- url     : https://prove2.me/theorems/c3fc7f0f-49e9-467a-855c-43808033dfbf
-- title:
--   P2 M Ground Theory Heights  Heights Inter log card eq sum log card localization b44963729dfe: P2 M Ground Theory Heights  Heights Inter log card eq sum log card localization b44963729dfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log card eq sum log card localization b44963729dfe construction uses the P2 M Ground Theory Heights  Heights Inter log card eq sum log card localization b44963729dfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L49-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocQuotCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter

theorem P2M_GroundTheory_Heights__Heights_Inter_log_card_eq_sum_log_card_localization_b44963729dfe (A : Type*) [CommRing A] [Finite A] [Fintype (PrimeSpectrum A)] :
    Real.log (Nat.card A) = ∑ p : PrimeSpectrum A, Real.log (Nat.card (Localization.AtPrime p.asIdeal)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«log_card_eq_sum_log_card_localization» := P2M_GroundTheory_Heights__Heights_Inter_log_card_eq_sum_log_card_localization_b44963729dfe
