-- Prove2me | Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
-- name    : P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:48:12.268659+00:00
-- url     : https://prove2.me/theorems/163c105a-7f71-4a2f-9c94-48b753a62367
-- title:
--   P2 M Nagata Factoriality Is Localization map mul mk  468d7c4e3210: P2 M Nagata Factoriality Is Localization map mul mk  468d7c4e3210
-- statement:
--   The P2 M Nagata Factoriality Is Localization map mul mk  468d7c4e3210 construction uses the P2 M Nagata Factoriality Is Localization map mul mk  468d7c4e3210 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L19-L22
-- source:
--   https://github.com/Arthur742Ramos/NagataFactoriality/blob/9ebcfa77a4f7eab6fdb663e7f151ceeb48abdff7/NagataFactoriality/Localization/IsLocalization.lean#L19-L22

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]

theorem P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210 (a b s : α) (hs : s ∈ S) :
    algebraMap α β a * _root_.IsLocalization.mk' β b ⟨s, hs⟩ =
      _root_.IsLocalization.mk' β (a * b) ⟨s, hs⟩ := by sorry

alias «NagataFactoriality».«IsLocalization».«map_mul_mk'» := P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
