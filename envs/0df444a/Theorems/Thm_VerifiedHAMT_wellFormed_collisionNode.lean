-- Prove2me | Theorems.Thm_VerifiedHAMT_wellFormed_collisionNode
-- name    : VerifiedHAMT.wellFormed_collisionNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:08.078877+00:00
-- url     : https://prove2.me/theorems/40f42019-e6ee-4132-ad91-2d26fa48f3c3
-- title:
--   Verified HAMT: well Formed collision Node
-- statement:
--   The Verified HAMT construction uses the well Formed collision Node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L153-L157
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Basic.lean#L153-L157

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

theorem VerifiedHAMT.wellFormed_collisionNode (hashAt : α → USize) (b : CollisionNode α β) :
    WellFormed hashAt b.val := by sorry
