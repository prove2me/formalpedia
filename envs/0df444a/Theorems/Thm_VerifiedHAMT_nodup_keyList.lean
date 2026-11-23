-- Prove2me | Theorems.Thm_VerifiedHAMT_nodup_keyList
-- name    : VerifiedHAMT.nodup_keyList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:36.0998+00:00
-- url     : https://prove2.me/theorems/cdbef213-0325-4188-9148-3a3dce136190
-- title:
--   Verified HAMT: nodup key List
-- statement:
--   Under the invariants no key is listed twice: routing separates the slots, and
--   uniqueness the keys of a collision node.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L120-L164
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Size.lean#L120-L164

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

theorem VerifiedHAMT.nodup_keyList {hashAt : α → USize} {node : Node α β} (wf : WellFormed hashAt node)
    (hu : Unique node) : (keyList node).Nodup := by sorry
