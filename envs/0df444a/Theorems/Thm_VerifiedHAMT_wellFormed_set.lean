-- Prove2me | Theorems.Thm_VerifiedHAMT_wellFormed_set
-- name    : VerifiedHAMT.wellFormed_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:55.854842+00:00
-- url     : https://prove2.me/theorems/14833fab-e975-41d1-934a-a9c2efaca036
-- title:
--   Verified HAMT: well Formed set
-- statement:
--   The Verified HAMT construction uses the well Formed set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Bindings.lean#L21-L29
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Bindings.lean#L21-L29

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

theorem VerifiedHAMT.wellFormed_set {hashAt : α → USize} {es : Array (Entry α β (Node α β))}
    (wf : WellFormed hashAt (.entries es)) (i : Nat) (hi : i < es.size)
    (e : Entry α β (Node α β))
    (route : ∀ q, EntryHasKey q e → slot (hashAt q) = i)
    (child : ∀ n, e = .ref n → WellFormed (fun q => nextHash (hashAt q)) n) :
    WellFormed hashAt (.entries (es.set i e)) := by sorry
