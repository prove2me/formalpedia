-- Prove2me | Theorems.Thm_VerifiedHAMT_updated_set
-- name    : VerifiedHAMT.updated_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:58.425719+00:00
-- url     : https://prove2.me/theorems/f1be7bb7-9f7a-4b05-a51e-663ab7500257
-- title:
--   Verified HAMT: updated set
-- statement:
--   The Verified HAMT construction uses the updated set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Bindings.lean#L38-L49
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Bindings.lean#L38-L49

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Definitions.Def_VerifiedHAMT_Bindings
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open Lean.PersistentHashMap
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.updated_set {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (key : α) (value : β)
    (hi : slot (hashAt key) < es.size) (e : Entry α β (Node α β))
    (upd : ∀ q w, EntryHasBinding q w e ↔
      (q = key ∧ w = value) ∨ (q ≠ key ∧ EntryHasBinding q w es[slot (hashAt key)])) :
    Updated (.entries es) (.entries (es.set (slot (hashAt key)) e)) key value := by sorry
