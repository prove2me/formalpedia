-- Prove2me | Theorems.Thm_VerifiedHAMT_findNode_entries
-- name    : VerifiedHAMT.findNode_entries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:36:11.928274+00:00
-- url     : https://prove2.me/theorems/224f4140-41cc-41ef-ac69-688291528109
-- title:
--   Verified HAMT: find Node entries
-- statement:
--   The Verified HAMT construction uses the find Node entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L51-L63
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L51-L63

module
public import Definitions.Def_VerifiedHAMT_Contains
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Find
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.findNode_entries [BEq α] (es : Array (Entry α β (Node α β)))
    (hash : USize) (key : α) :
    findNode (.entries es) hash key =
      if hi : slot hash < es.size then
        match es[slot hash] with
        | .null => none
        | .entry key' value => if key == key' then some value else none
        | .ref child => findNode child (nextHash hash) key
      else none := by sorry
