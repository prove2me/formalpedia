-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_hasKey_set_iff
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.hasKey_set_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:38:28.602047+00:00
-- url     : https://prove2.me/theorems/c2130d46-a7ab-44a4-bcb8-fdae24df1720
-- title:
--   Raw: has Key set iff
-- statement:
--   The Raw construction uses the has Key set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L112-L117
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Basic.lean#L112-L117

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_hasKey_set_iff

set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)

theorem VerifiedHAMT.SetWithoutValArray.Raw.hasKey_set_iff {es : Array (Entry α (Node α))}
    (i : Nat) (hi : i < es.size) (e : Entry α (Node α)) (key : α)
    (mem : ∀ q, EntryHasKey q e ↔ q = key ∨ EntryHasKey q es[i]) (q : α) :
    HasKey q (.entries (es.set i e)) ↔ q = key ∨ HasKey q (.entries es) := by sorry
