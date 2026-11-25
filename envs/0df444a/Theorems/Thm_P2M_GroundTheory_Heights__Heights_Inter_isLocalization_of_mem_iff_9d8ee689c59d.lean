-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isLocalization_of_mem_iff_9d8ee689c59d
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isLocalization_of_mem_iff_9d8ee689c59d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:20.373843+00:00
-- url     : https://prove2.me/theorems/32e700dc-7699-4c06-ad46-088837b9d01d
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Localization of mem iff 9d8ee689c59d: P2 M Ground Theory Heights  Heights Inter is Localization of mem iff 9d8ee689c59d
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Localization of mem iff 9d8ee689c59d construction uses the P2 M Ground Theory Heights  Heights Inter is Localization of mem iff 9d8ee689c59d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LocQuotCard.lean#L6-L23

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

theorem P2M_GroundTheory_Heights__Heights_Inter_isLocalization_of_mem_iff_9d8ee689c59d {O F : Type*} [CommRing O] [Field F] (φ : O →+* F) (hφ : Function.Injective φ)
    (L : Subring F) [Algebra O L] (hL : ∀ x : O, ((algebraMap O L x : L) : F) = φ x) (m : Ideal O) [m.IsPrime]
    (h : ∀ y : F, y ∈ L ↔ ∃ x s : O, s ∉ m ∧ y * φ s = φ x) :
    IsLocalization.AtPrime L m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isLocalization_of_mem_iff» := P2M_GroundTheory_Heights__Heights_Inter_isLocalization_of_mem_iff_9d8ee689c59d
