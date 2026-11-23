-- Prove2me | Theorems.Thm_VerifiedHAMT_insertNoExpand_wf_mem
-- name    : VerifiedHAMT.insertNoExpand_wf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:20.9907+00:00
-- url     : https://prove2.me/theorems/e64f0ee0-de75-4401-b6ce-4cf191264163
-- title:
--   Verified HAMT: insert No Expand wf mem
-- statement:
--   The Verified HAMT construction uses the insert No Expand wf mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L124-L135
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/InsertProofs.lean#L124-L135

module
public import Definitions.Def_VerifiedHAMT_Insert
public import Definitions.Def_VerifiedHAMT_Size
public import Definitions.Def_VerifiedHAMT_Util
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Init.Data.Array.Basic
import all Init.Data.Array.Basic
public import Definitions.Def_VerifiedHAMT_InsertProofs
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.insertNoExpand_wf_mem [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) (value : β) :
    letI res := insertNoExpand node (hashAt key) key value
    WellFormed hashAt res ∧ ∀ q, HasKey q res ↔ q = key ∨ HasKey q node := by sorry
