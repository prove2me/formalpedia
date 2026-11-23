-- Prove2me | Theorems.Thm_VerifiedHAMT_Map_toRaw_ofRaw
-- name    : VerifiedHAMT.Map.toRaw_ofRaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:53:08.316272+00:00
-- url     : https://prove2.me/theorems/19416a0f-ad6c-45d9-b2fb-7134d4125907
-- title:
--   Map: to Raw of Raw
-- statement:
--   The Map construction uses the to Raw of Raw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L99-L101
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/Map.lean#L99-L101

module
public import Definitions.Def_VerifiedHAMT_InsertProofs
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
public import Definitions.Def_VerifiedHAMT_Find
public import Lean.Data.PersistentHashMap
import all Lean.Data.PersistentHashMap
public import Batteries.Tactic.Alias
public import Definitions.Def_VerifiedHAMT_Map
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
open VerifiedHAMT.Map
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

theorem VerifiedHAMT.Map.toRaw_ofRaw (raw : Lean.PersistentHashMap α β)
    (valid : Valid raw) (unique : Unique raw.root) :
    (ofRaw raw valid unique).toRaw = raw := by sorry
