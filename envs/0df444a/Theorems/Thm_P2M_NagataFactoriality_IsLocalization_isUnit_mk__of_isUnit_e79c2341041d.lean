-- Prove2me | Theorems.Thm_P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_isUnit_e79c2341041d
-- name    : P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_isUnit_e79c2341041d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:43.310496+00:00
-- url     : https://prove2.me/theorems/66f233eb-be9e-4b20-a623-ef725bc0fad1
-- title:
--   P2 M Nagata Factoriality Is Localization is Unit mk  of is Unit e79c2341041d: P2 M Nagata Factoriality Is Localization is Unit mk  of is Unit e79c2341041d
-- statement:
--   The P2 M Nagata Factoriality Is Localization is Unit mk  of is Unit e79c2341041d construction uses the P2 M Nagata Factoriality Is Localization is Unit mk  of is Unit e79c2341041d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L105-L115
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L105-L115

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_isUnit_e79c2341041d {a s : α} (ha : IsUnit a) (hs : s ∈ S) :
    IsUnit (_root_.IsLocalization.mk' β a ⟨s, hs⟩) := by sorry

alias «NagataFactoriality».«IsLocalization».«isUnit_mk'_of_isUnit» := P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_isUnit_e79c2341041d
