-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_nodup_keyList
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.nodup_keyList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:37:09.253913+00:00
-- url     : https://prove2.me/theorems/a4239d2f-17d9-42d8-8fde-14d6c31a6391
-- title:
--   Raw: nodup key List
-- statement:
--   Under the invariants no key is listed twice: routing separates the slots, and
--   uniqueness the keys of a collision node.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L117-L161
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L117-L161

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.nodup_keyList {hashAt : α → USize} {node : Node α} (wf : WellFormed hashAt node)
    (hu : Unique node) : (keyList node).Nodup := by sorry
