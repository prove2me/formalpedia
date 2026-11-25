-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_eq_card_localization_38fca17f945a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_eq_card_localization_38fca17f945a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:18.771812+00:00
-- url     : https://prove2.me/theorems/6fdc9550-c4b3-453d-b532-e5c03c32684a
-- title:
--   P2 M Ground Theory Heights  Heights Inter card quot span eq card localization 38fca17f945a: P2 M Ground Theory Heights  Heights Inter card quot span eq card localization 38fca17f945a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter card quot span eq card localization 38fca17f945a construction uses the P2 M Ground Theory Heights  Heights Inter card quot span eq card localization 38fca17f945a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L40-L47

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

theorem P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_eq_card_localization_38fca17f945a {O L : Type*} [CommRing O] [CommRing L] (ψ : O →+* L) (b : O)
    (m : Ideal O) [m.IsPrime] (p : Ideal (O ⧸ Ideal.span {b})) [p.IsPrime]
    (hm : m = p.comap (Ideal.Quotient.mk _)) (h : @IsLocalization O _ m.primeCompl L _ ψ.toAlgebra) :
    Nat.card (L ⧸ Ideal.span {ψ b}) = Nat.card (Localization.AtPrime p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«card_quot_span_eq_card_localization» := P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_eq_card_localization_38fca17f945a
