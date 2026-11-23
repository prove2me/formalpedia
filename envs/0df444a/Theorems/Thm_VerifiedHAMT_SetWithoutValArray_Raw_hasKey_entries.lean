-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_entries
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.hasKey_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:29.764965+00:00
-- url     : https://prove2.me/theorems/ee01bc78-2c2c-4e80-9b2f-d7449d618e40
-- title:
--   Raw: has Key entries
-- statement:
--   The Raw construction uses the has Key entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L95-L110
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L95-L110

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_entries

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.hasKey_entries {es : Array (Entry α (Node α))} {key : α} :
    HasKey key (.entries es) ↔ ∃ (i : Nat) (hi : i < es.size), EntryHasKey key es[i] := by sorry
