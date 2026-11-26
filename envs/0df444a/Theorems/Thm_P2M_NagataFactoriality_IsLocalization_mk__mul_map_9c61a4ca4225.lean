-- Prove2me | Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
-- name    : P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:01.381564+00:00
-- url     : https://prove2.me/theorems/1008623e-3a41-5711-b857-9dd6f9858458
-- title:
--   P2 M Nagata Factoriality Is Localization mk  mul map 9c61a4ca4225: P2 M Nagata Factoriality Is Localization mk  mul map 9c61a4ca4225
-- statement:
--   The P2 M Nagata Factoriality Is Localization mk  mul map 9c61a4ca4225 construction uses the P2 M Nagata Factoriality Is Localization mk  mul map 9c61a4ca4225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L11-L13
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L11-L13

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225 (a s : α) (hs : s ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ * algebraMap α β s = algebraMap α β a := by sorry

alias «NagataFactoriality».«IsLocalization».«mk'_mul_map» := P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
