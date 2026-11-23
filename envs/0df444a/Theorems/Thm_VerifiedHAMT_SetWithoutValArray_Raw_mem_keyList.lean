-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_mem_keyList
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.mem_keyList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:21.331506+00:00
-- url     : https://prove2.me/theorems/ef0210b2-b29a-4847-b114-8dbf52ccd747
-- title:
--   Raw: mem key List
-- statement:
--   The listed keys are exactly the stored keys.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L70-L82
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L70-L82

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.mem_keyList {hashAt : α → USize} {node : Node α} (wf : WellFormed hashAt node)
    (key : α) : key ∈ keyList node ↔ HasKey key node := by sorry
