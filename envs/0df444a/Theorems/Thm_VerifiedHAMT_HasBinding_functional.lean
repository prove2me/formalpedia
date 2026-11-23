-- Prove2me | Theorems.Thm_VerifiedHAMT_HasBinding_functional
-- name    : VerifiedHAMT.HasBinding.functional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:11.812794+00:00
-- url     : https://prove2.me/theorems/90479564-09d0-47a8-b362-2fb8d9505a46
-- title:
--   Has Binding: functional
-- statement:
--   Routing and uniqueness make structural bindings single-valued.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L281-L306
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L281-L306

module
public import Lean.Data.PersistentHashMap
public import Std
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Basic
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.HasBinding.functional {hashAt : α → USize} {node : Node α β}
    (wf : WellFormed hashAt node) (hu : Unique node) {key : α} {v w : β}
    (hv : HasBinding key v node) (hw : HasBinding key w node) : v = w := by sorry
