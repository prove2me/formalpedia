-- Prove2me | Theorems.Thm_P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
-- name    : P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:07.959713+00:00
-- url     : https://prove2.me/theorems/d227dce5-ac6b-48c1-bc6b-f32ea035f9bd
-- title:
--   P2 M Nagata Factoriality Is Localization is Unit mk  of mem b89487295096: P2 M Nagata Factoriality Is Localization is Unit mk  of mem b89487295096
-- statement:
--   The P2 M Nagata Factoriality Is Localization is Unit mk  of mem b89487295096 construction uses the P2 M Nagata Factoriality Is Localization is Unit mk  of mem b89487295096 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L93-L97
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L93-L97

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096 {a s : α} (ha : a ∈ S) (hs : s ∈ S) :
    IsUnit (_root_.IsLocalization.mk' β a ⟨s, hs⟩) := by sorry

alias «NagataFactoriality».«IsLocalization».«isUnit_mk'_of_mem» := P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
