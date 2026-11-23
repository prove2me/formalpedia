-- Prove2me | Theorems.Thm_VerifiedHAMT_containsNode_eq_true_iff
-- name    : VerifiedHAMT.containsNode_eq_true_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:52.766614+00:00
-- url     : https://prove2.me/theorems/f0d5bf1c-4578-4c6e-8fb8-3162385451bf
-- title:
--   Verified HAMT: contains Node eq true iff
-- statement:
--   The Verified HAMT construction uses the contains Node eq true iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L109-L112
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Contains.lean#L109-L112

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Contains
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.containsNode_eq_true_iff [BEq α] [LawfulBEq α] {hashAt : α → USize}
    {node : Node α β} (wf : WellFormed hashAt node) (key : α) :
    containsNode node (hashAt key) key = true ↔ HasKey key node := by sorry
