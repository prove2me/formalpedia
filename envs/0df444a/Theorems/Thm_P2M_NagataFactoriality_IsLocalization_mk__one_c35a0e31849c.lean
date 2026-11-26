-- Prove2me | Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
-- name    : P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:03.330074+00:00
-- url     : https://prove2.me/theorems/06b9a07c-2389-5bfd-9c1e-e47107c56a13
-- title:
--   P2 M Nagata Factoriality Is Localization mk  one c35a0e31849c: P2 M Nagata Factoriality Is Localization mk  one c35a0e31849c
-- statement:
--   The P2 M Nagata Factoriality Is Localization mk  one c35a0e31849c construction uses the P2 M Nagata Factoriality Is Localization mk  one c35a0e31849c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L15-L17
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L15-L17

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c (a : α) :
    _root_.IsLocalization.mk' β a ⟨1, S.one_mem⟩ = algebraMap α β a := by sorry

alias «NagataFactoriality».«IsLocalization».«mk'_one» := P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
