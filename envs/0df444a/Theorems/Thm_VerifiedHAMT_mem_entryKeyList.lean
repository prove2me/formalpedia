-- Prove2me | Theorems.Thm_VerifiedHAMT_mem_entryKeyList
-- name    : VerifiedHAMT.mem_entryKeyList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:32.824043+00:00
-- url     : https://prove2.me/theorems/f506e816-7c25-4e94-a591-93dcc8e91fee
-- title:
--   Verified HAMT: mem entry Key List
-- statement:
--   An entry lists exactly its structural keys, given that its child does.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L64-L70
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L64-L70

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

theorem VerifiedHAMT.mem_entryKeyList {key : α} {e : Entry α β (Node α β)}
    (child : ∀ c, e = .ref c → (key ∈ keyList c ↔ HasKey key c)) :
    key ∈ entryKeyList e ↔ EntryHasKey key e := by sorry
