-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_quot_map_eq_card_localization_56ac6aa9ef55
-- name    : P2M_GroundTheory_Heights__Heights_Inter_card_quot_map_eq_card_localization_56ac6aa9ef55
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:22:55.596627+00:00
-- url     : https://prove2.me/theorems/954baabe-6812-5a1b-8e90-2624d2a5d963
-- title:
--   P2 M Ground Theory Heights  Heights Inter card quot map eq card localization 56ac6aa9ef55: P2 M Ground Theory Heights  Heights Inter card quot map eq card localization 56ac6aa9ef55
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter card quot map eq card localization 56ac6aa9ef55 construction uses the P2 M Ground Theory Heights  Heights Inter card quot map eq card localization 56ac6aa9ef55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L25-L38

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

theorem P2M_GroundTheory_Heights__Heights_Inter_card_quot_map_eq_card_localization_56ac6aa9ef55 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (p : Ideal (R ⧸ I)) [p.IsPrime] [IsLocalization.AtPrime S (p.comap (Ideal.Quotient.mk I))] :
    Nat.card (S ⧸ I.map (algebraMap R S)) = Nat.card (Localization.AtPrime p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«card_quot_map_eq_card_localization» := P2M_GroundTheory_Heights__Heights_Inter_card_quot_map_eq_card_localization_56ac6aa9ef55
