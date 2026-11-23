-- Prove2me | Theorems.Thm_VerifiedHAMT_findD_eq_of_not_mem
-- name    : VerifiedHAMT.findD_eq_of_not_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:36:29.934034+00:00
-- url     : https://prove2.me/theorems/25294333-d3b7-411d-aef5-66c4027401b2
-- title:
--   Verified HAMT: find D eq of not mem
-- statement:
--   The Verified HAMT construction uses the find D eq of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L276-L280
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Find.lean#L276-L280

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

theorem VerifiedHAMT.findD_eq_of_not_mem [BEq α] [LawfulBEq α] [Hashable α]
    (map : Lean.PersistentHashMap α β) (wf : Valid map)
    (key : α) (fallback : β) (hm : ¬ Mem key map) :
    findD map key fallback = fallback := by sorry
