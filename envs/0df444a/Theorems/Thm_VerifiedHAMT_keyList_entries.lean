-- Prove2me | Theorems.Thm_VerifiedHAMT_keyList_entries
-- name    : VerifiedHAMT.keyList_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:19.092124+00:00
-- url     : https://prove2.me/theorems/097af865-a6b4-4f49-ab75-a96bdf0b4846
-- title:
--   Verified HAMT: key List entries
-- statement:
--   The Verified HAMT construction uses the key List entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L54-L57
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L54-L57

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.keyList_entries (es : Array (Entry α β (Node α β))) :
    keyList (.entries es) = es.toList.flatMap entryKeyList := by sorry
