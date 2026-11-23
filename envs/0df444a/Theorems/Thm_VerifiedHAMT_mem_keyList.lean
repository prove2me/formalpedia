-- Prove2me | Theorems.Thm_VerifiedHAMT_mem_keyList
-- name    : VerifiedHAMT.mem_keyList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:21.959805+00:00
-- url     : https://prove2.me/theorems/5f90d1e6-cfaf-4ede-959a-3ed051c134a6
-- title:
--   Verified HAMT: mem key List
-- statement:
--   The listed keys are exactly the stored keys.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L73-L85
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L73-L85

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

theorem VerifiedHAMT.mem_keyList {hashAt : α → USize} {node : Node α β} (wf : WellFormed hashAt node)
    (key : α) : key ∈ keyList node ↔ HasKey key node := by sorry
