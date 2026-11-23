-- Prove2me | Theorems.Thm_VerifiedHAMT_containsThenInsert_eq_impl
-- name    : VerifiedHAMT.containsThenInsert_eq_impl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:41:50.833496+00:00
-- url     : https://prove2.me/theorems/ed22dcce-1c52-4b84-8737-2bc4b56260e4
-- title:
--   Verified HAMT: contains Then Insert eq impl
-- statement:
--   This equality is valid even for malformed nodes and unlawful key equality.
--
--   Source: https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/ContainsThenInsert.lean#L32-L36
-- source:
--   https://github.com/verse-lab/VerifiedHAMT/blob/244601f8deb02c0d6d8f855bebc4bbe368ad0c98/VerifiedHAMT/ContainsThenInsert.lean#L32-L36

module
public import Definitions.Def_VerifiedHAMT_InsertSized
public import Definitions.Def_VerifiedHAMT_ContainsThenInsert
set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT
variable {α : Type u} {β : Type v}

theorem VerifiedHAMT.containsThenInsert_eq_impl : @containsThenInsert = @containsThenInsertImpl := by sorry
