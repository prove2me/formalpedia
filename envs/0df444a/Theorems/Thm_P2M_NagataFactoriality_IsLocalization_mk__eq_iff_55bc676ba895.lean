-- Prove2me | Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895
-- name    : P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:18.540225+00:00
-- url     : https://prove2.me/theorems/b47a69cb-e6e9-5b3f-8e58-23d0d17bd0ed
-- title:
--   P2 M Nagata Factoriality Is Localization mk  eq iff 55bc676ba895: P2 M Nagata Factoriality Is Localization mk  eq iff 55bc676ba895
-- statement:
--   The P2 M Nagata Factoriality Is Localization mk  eq iff 55bc676ba895 construction uses the P2 M Nagata Factoriality Is Localization mk  eq iff 55bc676ba895 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L37-L46
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L37-L46

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]

theorem P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895 {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ = _root_.IsLocalization.mk' β b ⟨t, ht⟩ ↔ a * t = b * s := by sorry

alias «NagataFactoriality».«IsLocalization».«mk'_eq_iff» := P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895
