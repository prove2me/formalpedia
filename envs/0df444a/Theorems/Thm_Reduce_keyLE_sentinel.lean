-- Prove2me | Theorems.Thm_Reduce_keyLE_sentinel
-- name    : Reduce.keyLE_sentinel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:13:12.33744+00:00
-- url     : https://prove2.me/theorems/840eb367-b444-4e9c-ad7a-4cc08d4a94ec
-- title:
--   Reduce: key LE sentinel
-- statement:
--   The sentinel key `(.inl false, .inl false)` is the least key: `.inl false` is the
--   least `RawPointer`, so it is `≤` every key. Used as the initial `curkey` in `step`.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Process.lean#L37-L48
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Process.lean#L37-L48

import Definitions.Def_Bdd_Reduce_Populate
import Definitions.Def_Bdd_Reduce_Process
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.keyLE_sentinel (a : RawPointer × RawPointer) :
    KeyLE ((.inl false : RawPointer), (.inl false : RawPointer)) a := by sorry
