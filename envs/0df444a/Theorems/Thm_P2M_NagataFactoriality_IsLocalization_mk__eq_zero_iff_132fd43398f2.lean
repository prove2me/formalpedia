-- Prove2me | Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__eq_zero_iff_132fd43398f2
-- name    : P2M_NagataFactoriality_IsLocalization_mk__eq_zero_iff_132fd43398f2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T05:49:35.355133+00:00
-- url     : https://prove2.me/theorems/ba90163d-1e61-5307-83ac-808dfe798488
-- title:
--   P2 M Nagata Factoriality Is Localization mk  eq zero iff 132fd43398f2: P2 M Nagata Factoriality Is Localization mk  eq zero iff 132fd43398f2
-- statement:
--   The P2 M Nagata Factoriality Is Localization mk  eq zero iff 132fd43398f2 construction uses the P2 M Nagata Factoriality Is Localization mk  eq zero iff 132fd43398f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L52-L55
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L52-L55

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem P2M_NagataFactoriality_IsLocalization_mk__eq_zero_iff_132fd43398f2 {a s : α} (hs : s ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ = 0 ↔ a = 0 := by sorry

alias «NagataFactoriality».«IsLocalization».«mk'_eq_zero_iff» := P2M_NagataFactoriality_IsLocalization_mk__eq_zero_iff_132fd43398f2
