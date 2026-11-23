-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_entryKeyList
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.mem_entryKeyList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:08.590681+00:00
-- url     : https://prove2.me/theorems/003da143-220d-499c-b552-cc6591a3e469
-- title:
--   Raw: mem entry Key List
-- statement:
--   An entry lists exactly its structural keys, given that its child does.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L61-L67
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L61-L67

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.mem_entryKeyList {key : α} {e : Entry α (Node α)}
    (child : ∀ c, e = .ref c → (key ∈ keyList c ↔ HasKey key c)) :
    key ∈ entryKeyList e ↔ EntryHasKey key e := by sorry
