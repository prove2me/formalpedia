-- Prove2me | Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_entryListKeyList_eq_flatMap
-- name    : VerifiedHAMT.SetWithoutValArray.Raw.entryListKeyList_eq_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:40:17.360671+00:00
-- url     : https://prove2.me/theorems/97fe349a-bee2-43cb-8428-06d248388eef
-- title:
--   Raw: entry List Key List eq flat Map
-- statement:
--   The Raw construction uses the entry List Key List eq flat Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L46-L50
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/SetWithoutValArray/Size.lean#L46-L50

module
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Size
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}

theorem VerifiedHAMT.SetWithoutValArray.Raw.entryListKeyList_eq_flatMap (es : List (Entry α (Node α))) :
    entryListKeyList es = es.flatMap entryKeyList := by sorry
